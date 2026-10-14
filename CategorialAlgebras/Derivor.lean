import Stemma
import Mathlib.CategoryTheory.Category.Basic
import CategorialAlgebras.PartialAlgebra

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Substitutions and derivors" =>

The generalized ep-derivors of Section `SGenEpDerivors` of the draft transform partial algebras
by interpreting every operation symbol of one signature as a term of another. This document
gathers what they rest on: substitutions of terms, how terms are evaluated after a substitution
and along a homomorphism, sets of existence equations, and derivors between many-sorted
signatures, which form the category $`\mathsf{Sig}_{\mathfrak{d}}`.

```lean
universe u v w u' v' u'' v''

namespace CategorialAlgebras

open Signature

variable {S : Type u}
```

# Substitutions

:::definition (label := "term.subst") (central := false) (title := "Substitution")
Let $`X` and $`Y` be $`S`-sorted sets of variables and $`f \colon X \to \mathrm{T}_{\Sigma}(Y)`
an $`S`-sorted mapping. The *substitution* determined by $`f` is the $`S`-sorted mapping
$`f^{\sharp} \colon \mathrm{T}_{\Sigma}(X) \to \mathrm{T}_{\Sigma}(Y)` that replaces every
variable $`x` by $`f(x)`: $`f^{\sharp}(x) = f(x)` and
$`f^{\sharp}(\sigma((P_j)_j)) = \sigma((f^{\sharp}(P_j))_j)`. It is the unique homomorphism of
$`\Sigma`-algebras of terms that extends $`f`.

```lean
def Term.subst {Sig : Signature.{u, v} S} {X Y : S → Type*} (f : ∀ s, X s → Term Sig Y s) :
    {s : S} → Term Sig X s → Term Sig Y s
  | _, .var x => f _ x
  | _, .app σ ts => .app σ fun j => Term.subst f (ts j)
```
:::

```lean
namespace Term

variable {Sig : Signature.{u, v} S}

@[simp] lemma subst_var {X Y : S → Type*} (f : ∀ s, X s → Term Sig Y s) {s : S} (x : X s) :
    (Term.var x : Term Sig X s).subst f = f s x := rfl

@[simp] lemma subst_app {X Y : S → Type*} (f : ∀ s, X s → Term Sig Y s) {ws : List S} {s : S}
    (σ : Sig ws s) (ts : (j : Fin ws.length) → Term Sig X (ws.get j)) :
    (Term.app σ ts).subst f = .app σ fun j => (ts j).subst f := rfl

/-- Substituting every variable by itself does nothing. -/
@[simp] lemma subst_var_eq {X : S → Type*} {s : S} (P : Term Sig X s) :
    P.subst (fun _ x => .var x) = P := by
  induction P with
  | var x => rfl
  | app σ ts ih => simp only [subst_app, ih]

/-- Substitutions compose. -/
lemma subst_subst {X Y Z : S → Type*} (f : ∀ s, X s → Term Sig Y s)
    (g : ∀ s, Y s → Term Sig Z s) {s : S} (P : Term Sig X s) :
    (P.subst f).subst g = P.subst fun s x => (f s x).subst g := by
  induction P with
  | var x => rfl
  | app σ ts ih => simp only [subst_app, ih]

/-- The value of an operation symbol applied to a family of partial values. -/
def appPart (A : PartialAlgebra.{u, v, w} Sig) {ws : List S} {s : S} (σ : Sig ws s)
    (p : (j : Fin ws.length) → Part (A (ws.get j))) : Part (A s) :=
  ⟨∃ h : ∀ j, (p j).Dom, (A.op σ fun j => (p j).get (h j)).Dom,
    fun h => (A.op σ fun j => (p j).get (h.1 j)).get h.2⟩

lemma eval_app {V : S → Type*} (A : PartialAlgebra.{u, v, w} Sig) (val : ∀ s, V s → A s)
    {ws : List S} {s : S} (σ : Sig ws s) (ts : (j : Fin ws.length) → Term Sig V (ws.get j)) :
    (Term.app σ ts).eval A val = appPart A σ fun j => (ts j).eval A val := rfl

end Term
```

The value of a term after a substitution is the value of the term under the valuation that
sends every variable to the value of its image, provided that all these values are defined
(Remark `RSubst` of the draft). The proviso cannot be dropped: if $`y` does not occur in
$`R`, then $`f^{\sharp}(R)` may be defined although $`f(y)` is not. The equality below is an
equality of partial values: it says at once that both sides are defined for the same
valuations and that then they are equal.

:::Stemma.lemma (label := "term.eval-subst") (central := false) (title := "Evaluation after a substitution")
Let $`\mathbf{A}` be a partial $`\Sigma`-algebra, $`f \colon X \to \mathrm{T}_{\Sigma}(Y)` an
$`S`-sorted mapping and $`a \colon Y \to A` a valuation such that $`f(x)^{\mathbf{A}}[a]` is
defined for every variable $`x`, and let $`f^{\mathbf{A}}[a] \colon X \to A` send $`x` to
$`f(x)^{\mathbf{A}}[a]`. Then, for every term $`R \in \mathrm{T}_{\Sigma}(X)`,
$`f^{\sharp}(R)^{\mathbf{A}}[a]` is defined if and only if $`R^{\mathbf{A}}[f^{\mathbf{A}}[a]]`
is, and then they are equal.

```lean
theorem Term.eval_subst {Sig : Signature.{u, v} S} {X Y : S → Type*}
    (A : PartialAlgebra.{u, v, w} Sig) (f : ∀ s, X s → Term Sig Y s) (a : ∀ s, Y s → A s)
    (hf : ∀ s x, ((f s x).eval A a).Dom) {s : S} (R : Term Sig X s) :
    (R.subst f).eval A a = R.eval A fun s x => ((f s x).eval A a).get (hf s x) := by
  induction R with
  | var x => exact (Part.some_get (hf _ x)).symm
  | app σ ts ih => simp only [subst_app, eval_app, ih]
```
:::

:::proof (of := "term.eval-subst")
By induction on $`R`. For a variable $`x`, both sides are $`f(x)^{\mathbf{A}}[a]`. For
$`R = \sigma((R_j)_j)`, $`f^{\sharp}(R) = \sigma((f^{\sharp}(R_j))_j)`, and the value of an
operation symbol applied to a family of terms only depends on the partial values of the terms,
which are equal by the induction hypothesis.
:::

:::Stemma.lemma (label := "term.eval-hom") (central := false) (title := "Homomorphisms preserve values of terms")
Let $`h \colon \mathbf{A} \to \mathbf{B}` be a homomorphism of partial $`\Sigma`-algebras and
$`a \colon X \to A` a valuation. If $`P^{\mathbf{A}}[a]` is defined, then
$`P^{\mathbf{B}}[h \circ a]` is defined and equal to $`h(P^{\mathbf{A}}[a])` (Remark `RHomTerm`
of the draft).

```lean
theorem Term.eval_hom {Sig : Signature.{u, v} S} {X : S → Type*}
    {A B : PartialAlgebra.{u, v, w} Sig} (h : PartialAlgebra.Hom A B) (a : ∀ s, X s → A s)
    {s : S} (P : Term Sig X s) (hP : (P.eval A a).Dom) :
    ∃ hB : (P.eval B fun s x => h.map s (a s x)).Dom,
      (P.eval B fun s x => h.map s (a s x)).get hB = h.map s ((P.eval A a).get hP) := by
  induction P with
  | var x => exact ⟨trivial, rfl⟩
  | app σ ts ih =>
    obtain ⟨hts, hop⟩ := hP
    choose hB hget using fun j => ih j (hts j)
    have e : (fun j => ((ts j).eval B fun s x => h.map s (a s x)).get (hB j)) =
        fun j => h.map _ (((ts j).eval A a).get (hts j)) := funext hget
    have hdom : (B.op σ fun j => ((ts j).eval B fun s x => h.map s (a s x)).get (hB j)).Dom := by
      rw [e]; exact h.map_dom σ _ hop
    refine ⟨⟨hB, hdom⟩, ?_⟩
    change (B.op σ _).get hdom = h.map _ ((A.op σ _).get hop)
    rw [h.map_op σ _ hop]
    exact Part.get_eq_get_of_eq _ _ (congrArg (B.op σ) e)
```
:::

:::proof (of := "term.eval-hom")
By induction on $`P`. For a variable it is the definition of $`h \circ a`. For
$`P = \sigma((P_j)_j)`, the $`P_j` are defined in $`\mathbf{B}` with values $`h(P_j^{\mathbf{A}}[a])`,
by the induction hypothesis, and, since $`h` is a homomorphism, $`\sigma` is defined on this
family and its value is $`h(P^{\mathbf{A}}[a])`.
:::

# Sets of existence equations

A set of existence equations of $`\Sigma` with variables in $`X` is a subset of
$`\mathrm{Eq}_{\Sigma}(X)`, the set of {name}`EEq`s. Such sets describe the domains of the
operation symbols of an ep-signature and of the sorts along a generalized ep-derivor.

:::definition (label := "eeq.holds-all") (central := false) (title := "Satisfaction of a set of existence equations")
Let $`\mathbf{A}` be a partial $`\Sigma`-algebra, $`a \colon X \to A` a valuation and
$`\mathcal{H} \subseteq \mathrm{Eq}_{\Sigma}(X)`. Then $`\mathbf{A} \models \mathcal{H}[a]` if
every existence equation of $`\mathcal{H}` holds in $`\mathbf{A}` under $`a`. For an
$`S`-sorted mapping $`f \colon X \to \mathrm{T}_{\Sigma}(Y)`, $`f^{\sharp}[\mathcal{H}]` is the
set of the equations $`f^{\sharp}(P) \overset{\mathrm{e}}{=} f^{\sharp}(Q)`, for
$`(P \overset{\mathrm{e}}{=} Q) \in \mathcal{H}`.

```lean
def EEq.HoldsAll {Sig : Signature.{u, v} S} {X : S → Type*} (A : PartialAlgebra.{u, v, w} Sig)
    (a : ∀ s, X s → A s) (H : Set (EEq Sig X)) : Prop :=
  ∀ e ∈ H, e.Holds A a

def EEq.subst {Sig : Signature.{u, v} S} {X Y : S → Type*} (f : ∀ s, X s → Term Sig Y s)
    (e : EEq Sig X) : EEq Sig Y :=
  ⟨e.sort, e.lhs.subst f, e.rhs.subst f⟩
```
:::

```lean
/-- An existence equation holds when both sides have a common value. -/
lemma EEq.holds_iff_mem {Sig : Signature.{u, v} S} {X : S → Type*}
    (A : PartialAlgebra.{u, v, w} Sig) (a : ∀ s, X s → A s) (e : EEq Sig X) :
    e.Holds A a ↔ ∃ x, x ∈ e.lhs.eval A a ∧ x ∈ e.rhs.eval A a := by
  constructor
  · rintro ⟨h₁, h₂, h⟩
    exact ⟨_, Part.get_mem h₁, h ▸ Part.get_mem h₂⟩
  · rintro ⟨x, ⟨h₁, e₁⟩, ⟨h₂, e₂⟩⟩
    exact ⟨h₁, h₂, e₁.trans e₂.symm⟩
```

:::corollary (label := "eeq.holds-subst") (central := false) (title := "Satisfaction after a substitution")
Under the hypotheses of Lemma {name}`Term.eval_subst`, for every
$`\mathcal{H} \subseteq \mathrm{Eq}_{\Sigma}(X)`,
$`\mathbf{A} \models f^{\sharp}[\mathcal{H}][a]` if and only if
$`\mathbf{A} \models \mathcal{H}[f^{\mathbf{A}}[a]]`.

```lean
theorem EEq.holdsAll_subst {Sig : Signature.{u, v} S} {X Y : S → Type*}
    (A : PartialAlgebra.{u, v, w} Sig) (f : ∀ s, X s → Term Sig Y s) (a : ∀ s, Y s → A s)
    (hf : ∀ s x, ((f s x).eval A a).Dom) (H : Set (EEq Sig X)) :
    EEq.HoldsAll A a (EEq.subst f '' H) ↔
      EEq.HoldsAll A (fun s x => ((f s x).eval A a).get (hf s x)) H := by
  have key : ∀ e : EEq Sig X, (e.subst f).Holds A a ↔
      e.Holds A fun s x => ((f s x).eval A a).get (hf s x) := by
    intro e
    simp only [EEq.holds_iff_mem, EEq.subst, Term.eval_subst A f a hf]
  simp only [EEq.HoldsAll, Set.forall_mem_image, key]
```
:::

:::proof (of := "eeq.holds-subst")
An existence equation $`f^{\sharp}(P) \overset{\mathrm{e}}{=} f^{\sharp}(Q)` holds under $`a`
if and only if $`P \overset{\mathrm{e}}{=} Q` holds under $`f^{\mathbf{A}}[a]`, since, by
Lemma {name}`Term.eval_subst`, the partial values of the two sides are the same.
:::

:::corollary (label := "eeq.holds-hom") (central := false) (title := "Homomorphisms preserve satisfaction")
Let $`h \colon \mathbf{A} \to \mathbf{B}` be a homomorphism of partial $`\Sigma`-algebras,
$`a \colon X \to A` a valuation and $`\mathcal{H} \subseteq \mathrm{Eq}_{\Sigma}(X)`. If
$`\mathbf{A} \models \mathcal{H}[a]`, then $`\mathbf{B} \models \mathcal{H}[h \circ a]`.

```lean
theorem EEq.holdsAll_hom {Sig : Signature.{u, v} S} {X : S → Type*}
    {A B : PartialAlgebra.{u, v, w} Sig} (h : PartialAlgebra.Hom A B) (a : ∀ s, X s → A s)
    {H : Set (EEq Sig X)} (hH : EEq.HoldsAll A a H) :
    EEq.HoldsAll B (fun s x => h.map s (a s x)) H := by
  intro e he
  obtain ⟨h₁, h₂, heq⟩ := hH e he
  obtain ⟨k₁, e₁⟩ := Term.eval_hom h a e.lhs h₁
  obtain ⟨k₂, e₂⟩ := Term.eval_hom h a e.rhs h₂
  exact ⟨k₁, k₂, by rw [e₁, e₂, heq]⟩
```
:::

:::proof (of := "eeq.holds-hom")
By Lemma {name}`Term.eval_hom`, both sides of each equation are defined in $`\mathbf{B}`
under $`h \circ a`, with values the images by $`h` of their values in $`\mathbf{A}`, which are
equal.
:::

# Variables of a word

The draft fixes the variables $`v^{s}_{n}` and lets $`\downarrow\mathbf{s}` be the variables of
a word $`\mathbf{s}`, one for each letter; it then identifies a family
$`(a_j)_{j \in |\mathbf{s}|} \in A_{\mathbf{s}}` with the valuation that sends the variable of
the $`j`-th letter to $`a_j`. The library takes this identification as a definition: the
variables of $`\mathbf{s}` are its positions, the position $`j` being a variable of sort
$`s_j`.

The terms that a derivor $`(\varphi, d)` assigns to a symbol of arity $`\mathbf{s}` have their
variables in $`\downarrow\varphi^{\star}(\mathbf{s})`, the positions of $`\mathbf{s}` with sorts
read through $`\varphi`. The library uses these variables directly, rather than the positions
of the word $`\varphi^{\star}(\mathbf{s})`: the two sets are the same, but, in Lean, reading the
sorts of $`\mathbf{s}` through $`\psi \circ \varphi` is the same as reading them through
$`\varphi` and then through $`\psi`, whereas $`(\psi \circ \varphi)^{\star}(\mathbf{s})` and
$`\psi^{\star}(\varphi^{\star}(\mathbf{s}))` are only provably equal words. This keeps the
composition of derivors free of transports.

:::definition (label := "word-var") (central := false) (title := "Variables of a word")
Let $`\varphi \colon S \to T` and $`\mathbf{s} \in S^{\star}`. For $`t \in T`, the variables of
sort $`t` of $`\downarrow\varphi^{\star}(\mathbf{s})` are the positions $`j \in |\mathbf{s}|`
with $`\varphi(s_j) = t`; we write $`v^{\mathbf{s}}_j` for the position $`j`. For
$`\varphi = \mathrm{id}_S` these are the variables $`\downarrow\mathbf{s}`. A family
$`\mathbf{b} = (b_j)_{j \in |\mathbf{s}|}` with $`b_j \in B_{\varphi(s_j)}` is identified with
the valuation of $`\downarrow\varphi^{\star}(\mathbf{s})` in $`B` that sends $`v^{\mathbf{s}}_j`
to $`b_j`.

```lean
def WordVar {T : Type u'} (φ : S → T) (ws : List S) (t : T) : Type :=
  {j : Fin ws.length // φ (ws.get j) = t}

def WordVar.val {T : Type u'} {φ : S → T} {ws : List S} {B : T → Type w}
    (b : (j : Fin ws.length) → B (φ (ws.get j))) : ∀ t, WordVar φ ws t → B t :=
  fun _ v => v.2 ▸ b v.1
```
:::

# Derivors

:::definition (label := "derivor") (central := false) (title := "Derivor")
A *derivor* from a many-sorted signature $`(S, \Sigma)` to another $`(T, \Lambda)` is a pair
$`(\varphi, d)` where $`\varphi \colon S \to T` and $`d` assigns to every
$`\sigma \in \Sigma_{\mathbf{s}, s}` a term
$`d(\sigma) \in \mathrm{T}_{\Lambda}(\downarrow\varphi^{\star}(\mathbf{s}))_{\varphi(s)}`.

```lean
structure Derivor {T : Type u'} (Sig : Signature.{u, v} S) (Lam : Signature.{u', v'} T) where
  /-- The mapping between sorts. -/
  sortMap : S → T
  /-- The term assigned to each operation symbol. -/
  op : ∀ {ws : List S} {s : S}, Sig ws s → Term Lam (WordVar sortMap ws) (sortMap s)
```
:::

A derivor translates every term of $`\Sigma` into a term of $`\Lambda`: a variable is replaced
by a term given in advance, and $`\sigma((R_j)_j)` by $`d(\sigma)` with the translations of the
$`R_j` substituted for its variables. In the draft the variables of sort $`s` are sent to
variables of sort $`\varphi(s)`; the library allows any term, which is what the composition of
derivors and the translation of $`\mathrm{QE}`$-equations with arbitrary variables need.

:::definition (label := "derivor.trans") (central := false) (title := "Translation of terms along a derivor")
Let $`(\varphi, d)` be a derivor from $`(S, \Sigma)` to $`(T, \Lambda)`, $`X` an $`S`-sorted
set, $`Y` a $`T`-sorted set and $`\rho` a mapping that sends every $`x \in X_s` to a term
$`\rho(x) \in \mathrm{T}_{\Lambda}(Y)_{\varphi(s)}`. The *translation*
$`d^{\sharp}_{\rho} \colon \mathrm{T}_{\Sigma}(X)_s \to \mathrm{T}_{\Lambda}(Y)_{\varphi(s)}` is
defined by recursion on terms:

1. (H1) $`d^{\sharp}_{\rho}(x) = \rho(x)`, for every variable $`x`;
2. (H2) $`d^{\sharp}_{\rho}(\sigma((R_j)_{j \in |\mathbf{r}|})) = (d^{\sharp}_{\rho}(R_j))^{\sharp}_{j \in |\mathbf{r}|}(d(\sigma))`,
   i.e., $`d(\sigma)` with $`d^{\sharp}_{\rho}(R_j)` substituted for $`v^{\mathbf{r}}_j`.

The mapping $`d^{\sharp}` of the draft, from $`\mathrm{T}_{\Sigma}(\downarrow\mathbf{s})` to
$`\mathrm{T}_{\Lambda}(\downarrow\varphi^{\star}(\mathbf{s}))`, is the translation along the
mapping that sends $`v^{\mathbf{s}}_j` to $`v^{\mathbf{s}}_j`.

```lean
namespace Derivor

variable {T : Type u'} {Sig : Signature.{u, v} S} {Lam : Signature.{u', v'} T}

def trans (d : Derivor Sig Lam) {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lam Y (d.sortMap s)) : {s : S} → Term Sig X s → Term Lam Y (d.sortMap s)
  | _, .var x => ρ _ x
  | _, .app σ ts => (d.op σ).subst fun _ v => v.2 ▸ d.trans ρ (ts v.1)

/-- The variable `v^𝐬_j` of `↓𝐬`, seen as a variable of `↓φ*(𝐬)`. -/
def wordVar (d : Derivor Sig Lam) {ws : List S} (s : S) (v : WordVar id ws s) :
    Term Lam (WordVar d.sortMap ws) (d.sortMap s) :=
  .var ⟨v.1, congrArg d.sortMap v.2⟩

/-- The translation `d♯` of the draft. -/
abbrev sharp (d : Derivor Sig Lam) {ws : List S} {s : S} (R : Term Sig (WordVar id ws) s) :
    Term Lam (WordVar d.sortMap ws) (d.sortMap s) :=
  d.trans d.wordVar R

end Derivor
```
:::

```lean
namespace Derivor

variable {T : Type u'} {Sig : Signature.{u, v} S} {Lam : Signature.{u', v'} T}

@[simp] lemma trans_var (d : Derivor Sig Lam) {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lam Y (d.sortMap s)) {s : S} (x : X s) :
    d.trans ρ (.var x) = ρ s x := rfl

lemma trans_app (d : Derivor Sig Lam) {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lam Y (d.sortMap s)) {ws : List S} {s : S} (σ : Sig ws s)
    (ts : (j : Fin ws.length) → Term Sig X (ws.get j)) :
    d.trans ρ (.app σ ts) = (d.op σ).subst fun _ v => v.2 ▸ d.trans ρ (ts v.1) := rfl

/-- A transport of the sort of a term commutes with its translation. -/
lemma trans_cast (d : Derivor Sig Lam) {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lam Y (d.sortMap s)) {s s' : S} (h : s = s') (R : Term Sig X s) :
    d.trans ρ (h ▸ R) = (congrArg d.sortMap h) ▸ d.trans ρ R := by
  subst h; rfl

end Derivor
```

:::Stemma.lemma (label := "derivor.trans-subst") (central := false) (title := "Translations commute with substitutions")
Let $`(\varphi, d)` be a derivor. Then translating a substituted term is translating the term
along the translations of the substituted terms:
$`d^{\sharp}_{\rho}(f^{\sharp}(Q)) = d^{\sharp}_{d^{\sharp}_{\rho} \circ f}(Q)`. Substituting in
a translated term is translating along the substituted images:
$`g^{\sharp}(d^{\sharp}_{\rho}(Q)) = d^{\sharp}_{g^{\sharp} \circ \rho}(Q)`. In particular,
$`d^{\sharp}((P_j)^{\sharp}_{j}(Q)) = (d^{\sharp}(P_j))^{\sharp}_{j}(d^{\sharp}(Q))`, as in the
draft.

```lean
theorem Derivor.trans_subst {T : Type u'} {Sig : Signature.{u, v} S}
    {Lam : Signature.{u', v'} T} (d : Derivor Sig Lam) {X X' : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X' s → Term Lam Y (d.sortMap s)) (f : ∀ s, X s → Term Sig X' s) {s : S}
    (Q : Term Sig X s) :
    d.trans ρ (Q.subst f) = d.trans (fun s x => d.trans ρ (f s x)) Q := by
  induction Q with
  | var x => rfl
  | app σ ts ih => simp only [Term.subst_app, trans_app, ih]

theorem Derivor.subst_trans {T : Type u'} {Sig : Signature.{u, v} S}
    {Lam : Signature.{u', v'} T} (d : Derivor Sig Lam) {X : S → Type*} {Y Y' : T → Type*}
    (ρ : ∀ s, X s → Term Lam Y (d.sortMap s)) (g : ∀ t, Y t → Term Lam Y' t) {s : S}
    (Q : Term Sig X s) :
    (d.trans ρ Q).subst g = d.trans (fun s x => (ρ s x).subst g) Q := by
  induction Q with
  | var x => rfl
  | app σ ts ih =>
    simp only [trans_app, Term.subst_subst]
    congr 1
    funext t v
    obtain ⟨j, hj⟩ := v
    subst hj
    exact ih j
```
:::

:::proof (of := "derivor.trans-subst")
Both by induction on $`Q`. For the first, the translation of $`\sigma((f^{\sharp}(Q_j))_j)` is
$`d(\sigma)` with the translations of the $`f^{\sharp}(Q_j)` substituted, which are those of
the $`Q_j` along $`d^{\sharp}_{\rho} \circ f` by the induction hypothesis. For the second,
substituting with $`g` after substituting the translations of the $`Q_j` in $`d(\sigma)` is
substituting their images by $`g^{\sharp}`, because substitutions compose.
:::

:::definition (label := "derivor.id-comp") (central := false) (title := "Identity and composite derivors")
The *identity* derivor at $`(S, \Sigma)` is $`(\mathrm{id}_S, \eta^{\Sigma})`, where
$`\eta^{\Sigma}(\sigma) = \sigma((v^{\mathbf{s}}_j)_{j \in |\mathbf{s}|})`, for
$`\sigma \in \Sigma_{\mathbf{s}, s}`. The *composite* of $`(\varphi, d)` from $`(S, \Sigma)` to
$`(T, \Lambda)` and $`(\psi, e)` from $`(T, \Lambda)` to $`(U, \Omega)` is
$`(\psi \circ \varphi, e^{\sharp} \circ d)`, where $`e^{\sharp}` sends the variable
$`v^{\mathbf{s}}_j` of $`\downarrow\varphi^{\star}(\mathbf{s})` to the variable
$`v^{\mathbf{s}}_j` of $`\downarrow(\psi \circ \varphi)^{\star}(\mathbf{s})`.

```lean
namespace Derivor

variable {T : Type u'} {U : Type u''} {Sig : Signature.{u, v} S}
  {Lam : Signature.{u', v'} T} {Om : Signature.{u'', v''} U}

def id (Sig : Signature.{u, v} S) : Derivor Sig Sig where
  sortMap s := s
  op σ := .app σ fun j => .var ⟨j, rfl⟩

def comp (e : Derivor Lam Om) (d : Derivor Sig Lam) : Derivor Sig Om where
  sortMap s := e.sortMap (d.sortMap s)
  op σ := e.trans (fun _ v => .var ⟨v.1, congrArg e.sortMap v.2⟩) (d.op σ)

end Derivor
```
:::

:::proposition (label := "derivor.trans-id-comp") (central := false) (title := "Translation along identities and composites")
Translating along the identity derivor is substituting:
$`(\eta^{\Sigma})^{\sharp}_{\rho}(R) = \rho^{\sharp}(R)`; in particular $`(\eta^{\Sigma})^{\sharp}`
is the identity. Translating along a composite is translating twice:
$`(e^{\sharp} \circ d)^{\sharp}_{e^{\sharp}_{\kappa} \circ \rho} = e^{\sharp}_{\kappa} \circ d^{\sharp}_{\rho}`
(property (H3) of the draft).

```lean
theorem Derivor.trans_id {Sig : Signature.{u, v} S} {X Y : S → Type*}
    (ρ : ∀ s, X s → Term Sig Y s) {s : S} (R : Term Sig X s) :
    (Derivor.id Sig).trans ρ R = R.subst ρ := by
  induction R with
  | var x => rfl
  | app σ ts ih =>
    simp only [trans_app, Term.subst_app, Derivor.id]
    congr 1
    funext j
    exact ih j

theorem Derivor.trans_comp {T : Type u'} {U : Type u''} {Sig : Signature.{u, v} S}
    {Lam : Signature.{u', v'} T} {Om : Signature.{u'', v''} U} (e : Derivor Lam Om)
    (d : Derivor Sig Lam) {X : S → Type*} {Y : T → Type*} {Z : U → Type*}
    (ρ : ∀ s, X s → Term Lam Y (d.sortMap s)) (κ : ∀ t, Y t → Term Om Z (e.sortMap t))
    {s : S} (R : Term Sig X s) :
    (e.comp d).trans (fun s x => e.trans κ (ρ s x)) R = e.trans κ (d.trans ρ R) := by
  induction R with
  | var x => rfl
  | app σ ts ih =>
    change (e.trans _ (d.op σ)).subst _ = e.trans κ ((d.op σ).subst _)
    rw [trans_subst]
    refine (subst_trans e _ _ (d.op σ)).trans ?_
    congr 1
    funext t v
    obtain ⟨j, hj⟩ := v
    subst hj
    exact ih j
```
:::

:::proof (of := "derivor.trans-id-comp")
Both by induction on terms. Along the identity, $`\sigma((R_j)_j)` becomes
$`\sigma((v^{\mathbf{s}}_j)_j)` with the translations of the $`R_j` substituted, that is,
$`\sigma` applied to them. Along the composite, $`\sigma((R_j)_j)` becomes
$`e^{\sharp}(d(\sigma))` with the translations of the $`R_j` substituted; by
Lemma {name}`Derivor.trans_subst` this is the translation along $`e` of $`d(\sigma)` with the
translations along $`d` of the $`R_j` substituted, which is
$`e^{\sharp}_{\kappa}(d^{\sharp}_{\rho}(\sigma((R_j)_j)))`.
:::

:::construction (label := "sig-d") (central := false) (title := "The category of signatures and derivors")
The many-sorted signatures, together with the derivors, their composition and the identity
derivors, form a category $`\mathsf{Sig}_{\mathfrak{d}}`, as in the draft.

```lean
/-- A many-sorted signature `(S, Σ)`. -/
structure ManySortedSignature where
  /-- The set of sorts. -/
  sorts : Type u
  /-- The signature. -/
  sig : Signature.{u, v} sorts

namespace Derivor

variable {T : Type u'} {Sig : Signature.{u, v} S} {Lam : Signature.{u', v'} T}

lemma ext_op {φ : S → T}
    {op op' : ∀ {ws : List S} {s : S}, Sig ws s → Term Lam (WordVar φ ws) (φ s)}
    (h : ∀ (ws : List S) (s : S) (σ : Sig ws s), op σ = op' σ) :
    (⟨φ, op⟩ : Derivor Sig Lam) = ⟨φ, op'⟩ := by
  have : @op = @op' := by funext ws s σ; exact h ws s σ
  subst this; rfl

lemma id_comp (d : Derivor Sig Lam) : (Derivor.id Lam).comp d = d := by
  obtain ⟨φ, op⟩ := d
  refine ext_op fun ws s σ => ?_
  exact (trans_id (X := WordVar φ ws) (fun _ v => .var v) (op σ)).trans (Term.subst_var_eq _)

lemma comp_id (d : Derivor Sig Lam) : d.comp (Derivor.id Sig) = d := by
  obtain ⟨φ, op⟩ := d
  refine ext_op fun ws s σ => ?_
  change (op σ).subst _ = op σ
  conv_rhs => rw [← Term.subst_var_eq (op σ)]
  congr 1
  funext t v
  obtain ⟨j, hj⟩ := v
  subst hj
  rfl

lemma comp_assoc {U : Type u''} {V : Type u} {Om : Signature.{u'', v''} U}
    {The : Signature.{u, v} V} (f : Derivor Om The) (e : Derivor Lam Om)
    (d : Derivor Sig Lam) : (f.comp e).comp d = f.comp (e.comp d) := by
  refine ext_op fun ws s σ => ?_
  exact (trans_comp f e
    (fun (t : T) (v : WordVar d.sortMap ws t) =>
      (.var ⟨v.1, congrArg e.sortMap v.2⟩ : Term Om (WordVar (e.comp d).sortMap ws) (e.sortMap t)))
    (fun (t : U) (v : WordVar (e.comp d).sortMap ws t) =>
      (.var ⟨v.1, congrArg f.sortMap v.2⟩ :
        Term The (WordVar (f.comp (e.comp d)).sortMap ws) (f.sortMap t)))
    (d.op σ))

end Derivor

-- Derivors between signatures in `Type u` with symbols in `Type v` live in `Type (max u v)`.
set_option linter.checkUnivs false in
instance : CategoryTheory.Category.{max u v} ManySortedSignature.{u, v} where
  Hom A B := Derivor A.sig B.sig
  id A := Derivor.id A.sig
  comp d e := e.comp d
  id_comp := Derivor.comp_id
  comp_id := Derivor.id_comp
  assoc d e f := (Derivor.comp_assoc f e d).symm
```
:::

```lean
end CategorialAlgebras
```
