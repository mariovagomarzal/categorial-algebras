import Stemma
import Mathlib.CategoryTheory.Functor.Basic
import CategorialAlgebras.EpSignature

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Generalized ep-derivors" =>

A generalized ep-derivor from an ep-signature $`\mathbf{\Sigma}` to another $`\mathbf{\Lambda}`
transforms partial $`\Lambda`-algebras into partial $`\Sigma`-algebras. Every sort $`s` of
$`\mathbf{\Sigma}` is sent to a sort $`\varphi(s)` of $`\mathbf{\Lambda}` together with a set
$`D_s` of existence equations in one variable, which carves out the elements of
$`B_{\varphi(s)}` that interpret $`s`; every operation symbol $`\sigma` is sent to a term
$`d(\sigma)`, which interprets it. The domain of $`\sigma` in the transformed algebra is not a
datum: it is computed from the domain conditions of $`\sigma`, by recursion along the
well-founded relation $`\lhd` of the ep-signature. This document follows Subsection
`SGenEpDerivorsDef` of the draft.

```lean
universe u v w u' v'

namespace CategorialAlgebras

open CategoryTheory Signature

variable {S : Type u} {T : Type u'}
```

# Partial algebras: the category, closed subsets and congruences

:::definition (label := "partial-algebra.category") (central := false) (title := "The category of partial algebras")
The partial $`\Sigma`-algebras and their homomorphisms form the category
$`\mathsf{PAlg}(\Sigma)`.

```lean
instance PartialAlgebra.category {Sig : Signature.{u, v} S} :
    Category.{max u w} (PartialAlgebra.{u, v, w} Sig) where
  Hom A B := PartialAlgebra.Hom A B
  id A := PartialAlgebra.Hom.id A
  comp H K := PartialAlgebra.Hom.comp K H
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
```
:::

:::definition (label := "partial-algebra.closed-congruence") (central := false) (title := "Closed subsets and congruences")
Let $`\mathbf{A}` be a partial $`\Sigma`-algebra. A *closed subset* of $`\mathbf{A}` is an
$`S`-sorted subset $`Y \subseteq A` such that, for every $`\sigma \in \Sigma_{\mathbf{s}, s}`
and every $`\mathbf{a} \in Y_{\mathbf{s}}` in the domain of $`F_\sigma`,
$`F_\sigma(\mathbf{a}) \in Y_s`. A *congruence* on $`\mathbf{A}` is an $`S`-sorted equivalence
$`\Phi` on $`A` such that, for every $`\sigma \in \Sigma_{\mathbf{s}, s}` and all
$`\mathbf{a}, \mathbf{b}` in the domain of $`F_\sigma` with $`(a_j, b_j) \in \Phi_{s_j}` for
every $`j`, $`(F_\sigma(\mathbf{a}), F_\sigma(\mathbf{b})) \in \Phi_s`.

```lean
def PartialAlgebra.IsClosed {Sig : Signature.{u, v} S} (A : PartialAlgebra.{u, v, w} Sig)
    (Y : ∀ s, Set (A s)) : Prop :=
  ∀ {ws : List S} {s : S} (σ : Sig ws s) (a : Arity A ws), (∀ j, a j ∈ Y _) →
    ∀ h : (A.op σ a).Dom, (A.op σ a).get h ∈ Y s

structure PartialAlgebra.IsCongruence {Sig : Signature.{u, v} S}
    (A : PartialAlgebra.{u, v, w} Sig) (Φ : ∀ s, A s → A s → Prop) : Prop where
  /-- Each `Φ_s` is an equivalence. -/
  equivalence : ∀ s, Equivalence (Φ s)
  /-- `Φ` is compatible with the operations, where they are defined. -/
  compat : ∀ {ws : List S} {s : S} (σ : Sig ws s) (a b : Arity A ws), (∀ j, Φ _ (a j) (b j)) →
    ∀ (ha : (A.op σ a).Dom) (hb : (A.op σ b).Dom), Φ s ((A.op σ a).get ha) ((A.op σ b).get hb)
```
:::

:::Stemma.lemma (label := "term.eval-closed-congruence") (central := false) (title := "Values of terms in closed subsets and congruences")
Let $`\mathbf{A}` be a partial $`\Sigma`-algebra and $`P` a term. If $`Y` is a closed subset
of $`\mathbf{A}` and $`a` a valuation in $`Y`, then $`P^{\mathbf{A}}[a]`, when defined, is in
$`Y`. If $`\Phi` is a congruence on $`\mathbf{A}` and $`a`, $`b` are valuations with
$`(a(x), b(x)) \in \Phi` for every variable $`x`, then $`P^{\mathbf{A}}[a]` and
$`P^{\mathbf{A}}[b]`, when both defined, are $`\Phi`-related.

```lean
theorem Term.eval_mem_closed {Sig : Signature.{u, v} S} {V : S → Type*}
    {A : PartialAlgebra.{u, v, w} Sig} {Y : ∀ s, Set (A s)} (hY : A.IsClosed Y)
    (a : ∀ s, V s → A s) (ha : ∀ s x, a s x ∈ Y s) {s : S} (P : Term Sig V s)
    (h : (P.eval A a).Dom) : (P.eval A a).get h ∈ Y s := by
  induction P with
  | var x => exact ha _ x
  | app σ ts ih => exact hY σ _ (fun j => ih j _) h.2

theorem Term.eval_congruence {Sig : Signature.{u, v} S} {V : S → Type*}
    {A : PartialAlgebra.{u, v, w} Sig} {Φ : ∀ s, A s → A s → Prop} (hΦ : A.IsCongruence Φ)
    (a b : ∀ s, V s → A s) (hab : ∀ s x, Φ s (a s x) (b s x)) {s : S} (P : Term Sig V s)
    (ha : (P.eval A a).Dom) (hb : (P.eval A b).Dom) :
    Φ s ((P.eval A a).get ha) ((P.eval A b).get hb) := by
  induction P with
  | var x => exact hab _ x
  | app σ ts ih => exact hΦ.compat σ _ _ (fun j => ih j _ _) ha.2 hb.2
```
:::

:::proof (of := "term.eval-closed-congruence")
Both by induction on $`P`. If $`\sigma((P_j)_j)` is defined, then so are the $`P_j`; their
values are in $`Y` (respectively, $`\Phi`-related) by the induction hypothesis, and $`Y` is
closed under $`F_\sigma` (respectively, $`\Phi` is compatible with $`F_\sigma`).
:::

# The single variable of a sort

The domain $`D_s` of a sort $`s` is a set of existence equations in the single variable of
$`\downarrow\varphi^{\star}((s))`, the variables of the one-letter word $`(s)` with sorts read
through $`\varphi` (see {name}`WordVar`); this variable has sort $`\varphi(s)`. A mapping on
these variables, a valuation or a substitution, is determined by its value at the single
variable.

```lean
/-- The single variable of the one-letter word `(s)`, read through `φ`, has sort `φ s`. -/
lemma WordVar.single_eq {φ : S → T} {s : S} {t : T} (v : WordVar φ [s] t) : φ s = t := by
  obtain ⟨j, h⟩ := v
  rw [← h, Fin.fin_one_eq_zero j]
  rfl

/-- The mapping on `↓φ*((s))` determined by its value at the single variable. -/
def WordVar.single {φ : S → T} {s : S} {F : T → Sort*} (x : F (φ s)) :
    ∀ t, WordVar φ [s] t → F t :=
  fun _ v => v.single_eq ▸ x

lemma Term.eval_cast {Sig : Signature.{u, v} S} {V : S → Type*} (A : PartialAlgebra.{u, v, w} Sig)
    (a : ∀ s, V s → A s) {s s' : S} (h : s = s') (P : Term Sig V s) :
    (h ▸ P).eval A a = h ▸ P.eval A a := by
  subst h; rfl

lemma Part.cast_dom {α : Type*} {F : α → Type*} {x y : α} (h : x = y) (p : Part (F x)) :
    (h ▸ p).Dom ↔ p.Dom := by
  subst h; rfl

/-- Substituting a term `P` for the single variable: all images are defined if `P` is. -/
lemma eval_single {Sig : Signature.{u', v} T} {Y : T → Type*} (A : PartialAlgebra.{u', v, w} Sig)
    (a : ∀ t, Y t → A t) {φ : S → T} {s : S} (P : Term Sig Y (φ s)) (hP : (P.eval A a).Dom) :
    ∀ t (x : WordVar φ [s] t), ((WordVar.single (F := fun t => Term Sig Y t) P t x).eval A a).Dom
  | t, x => by
    unfold WordVar.single
    rw [Term.eval_cast, Part.cast_dom]
    exact hP

lemma eval_single_get {Sig : Signature.{u', v} T} {Y : T → Type*}
    (A : PartialAlgebra.{u', v, w} Sig) (a : ∀ t, Y t → A t) {φ : S → T} {s : S}
    (P : Term Sig Y (φ s)) (hP : (P.eval A a).Dom) :
    (fun t x => ((WordVar.single (F := fun t => Term Sig Y t) P t x).eval A a).get
        (eval_single A a P hP t x)) =
      WordVar.single (F := fun t => A t) ((P.eval A a).get hP) := by
  funext t x
  unfold WordVar.single
  generalize x.single_eq = h
  subst h
  rfl

/-- Transports along `φ s = t` commute with sorted mappings. -/
lemma single_map {φ : S → T} {s : S} {F G : T → Sort*} (g : ∀ t, F t → G t) (x : F (φ s)) :
    (fun t v => g t (WordVar.single (φ := φ) (s := s) x t v)) = WordVar.single (g _ x) := by
  funext t v
  unfold WordVar.single
  generalize v.single_eq = h
  subst h
  rfl

lemma wordVar_val_map {φ : S → T} {ws : List S} {F G : T → Type*} (g : ∀ t, F t → G t)
    (b : (j : Fin ws.length) → F (φ (ws.get j))) :
    (fun t v => g t (WordVar.val (φ := φ) (B := F) b t v)) =
      WordVar.val (φ := φ) (B := G) fun j => g _ (b j) := by
  funext t v
  obtain ⟨j, h⟩ := v
  subst h
  rfl

lemma holdsAll_union {Sig : Signature.{u', v'} T} {Y : T → Type*}
    {A : PartialAlgebra.{u', v', w} Sig} {c : ∀ t, Y t → A t} {H H' : Set (EEq Sig Y)} :
    EEq.HoldsAll A c (H ∪ H') ↔ EEq.HoldsAll A c H ∧ EEq.HoldsAll A c H' :=
  ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

lemma holdsAll_iUnion {Sig : Signature.{u', v'} T} {Y : T → Type*} {ι : Sort*}
    {A : PartialAlgebra.{u', v', w} Sig} {c : ∀ t, Y t → A t} {H : ι → Set (EEq Sig Y)} :
    EEq.HoldsAll A c (⋃ i, H i) ↔ ∀ i, EEq.HoldsAll A c (H i) :=
  ⟨fun h i e he => h e (Set.mem_iUnion.2 ⟨i, he⟩),
    fun h e he => by obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he; exact h i e hi⟩
```

# Generalized ep-derivors

:::definition (label := "gen-ep-derivor") (central := false) (title := "Generalized ep-derivor")
Let $`\mathbf{\Sigma} = (S, \Sigma, \mathrm{def}^{\mathbf{\Sigma}})` and
$`\mathbf{\Lambda} = (T, \Lambda, \mathrm{def}^{\mathbf{\Lambda}})` be ep-signatures. A
*generalized ep-derivor* from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}` is a triple
$`\mathbf{d} = (\varphi, D, d)` where $`(\varphi, d)` is a derivor from $`(S, \Sigma)` to
$`(T, \Lambda)` and $`D` assigns to every sort $`s \in S` a set
$`D_s \subseteq \mathrm{Eq}_{\Lambda}(\downarrow\varphi^{\star}((s)))` of existence equations
in the single variable of $`\downarrow\varphi^{\star}((s))`, the *domain* of $`s`.

```lean
structure GenEpDerivor (Sg : EpSignature.{u, v} S) (Lg : EpSignature.{u', v'} T) extends
    Derivor Sg.sig Lg.sig where
  /-- The domain `D_s` of each sort. -/
  dom : ∀ s, Set (EEq Lg.sig (WordVar sortMap [s]))
```
:::

The set $`D_s` is the counterpart of the formula $`\Delta_s(x)` of the general derivors of
Lamo and Guerra, and $`d(\sigma)` that of the formula $`\Phi^{\sigma}`, which here is the
equation $`y = d(\sigma)`. A generalized ep-derivor carries no condition: whether it sends
models to models is a property of it, studied afterwards.

```lean
namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u', v'} T}
```

:::definition (label := "gen-ep-derivor.domains") (central := false) (title := "Domains of sorts and words")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}`. For a word $`\mathbf{s} \in S^{\star}`,
$`D_{\mathbf{s}} = \bigcup_{j \in |\mathbf{s}|} (\iota^{\mathbf{s}}_j)^{\sharp}[D_{s_j}]`, where
$`\iota^{\mathbf{s}}_j` renames the single variable to the variable $`v^{\mathbf{s}}_j` of
$`\downarrow\varphi^{\star}(\mathbf{s})`. For a partial $`\Lambda`-algebra $`\mathbf{B}`,
$`B_{(\varphi, D)}` is the $`S`-sorted set with
$`(B_{(\varphi, D)})_s = \{b \in B_{\varphi(s)} \mid \mathbf{B} \models D_s[b]\}`, and, for a
homomorphism $`f \colon \mathbf{B} \to \mathbf{B}'`, $`\Delta_{(\varphi, D)}(f)` is the
restriction of $`f_{\varphi} = (f_{\varphi(s)})_{s \in S}` to
$`B_{(\varphi, D)} \to B'_{(\varphi, D)}`, which is well defined because homomorphisms
preserve the satisfaction of existence equations.

```lean
/-- The renaming `ι^𝐬_j` of the single variable to the position `j`. -/
def iota (d : GenEpDerivor Sg Lg) {ws : List S} (j : Fin ws.length) :
    ∀ t, WordVar d.sortMap [ws.get j] t → Term Lg.sig (WordVar d.sortMap ws) t :=
  fun _ v => .var ⟨j, v.single_eq⟩

def domWord (d : GenEpDerivor Sg Lg) (ws : List S) : Set (EEq Lg.sig (WordVar d.sortMap ws)) :=
  ⋃ j : Fin ws.length, EEq.subst (d.iota j) '' d.dom (ws.get j)

def domCarrier (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig) (s : S) :
    Type w :=
  {b : B (d.sortMap s) // EEq.HoldsAll B (WordVar.single (F := fun t => B t) b) (d.dom s)}

def deltaMap (d : GenEpDerivor Sg Lg) {B B' : PartialAlgebra.{u', v', w} Lg.sig}
    (f : PartialAlgebra.Hom B B') (s : S) (b : d.domCarrier B s) : d.domCarrier B' s :=
  ⟨f.map _ b.1, by
    have := EEq.holdsAll_hom f _ b.2
    rwa [single_map (G := fun t => B' t)] at this⟩
```
:::

```lean
@[simp] lemma deltaMap_val (d : GenEpDerivor Sg Lg) {B B' : PartialAlgebra.{u', v', w} Lg.sig}
    (f : PartialAlgebra.Hom B B') (s : S) (b : d.domCarrier B s) :
    (d.deltaMap f s b).1 = f.map _ b.1 := rfl

lemma iota_eval (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig) {ws : List S}
    (b : (j : Fin ws.length) → B (d.sortMap (ws.get j))) (j : Fin ws.length) :
    ∀ t x, ((d.iota j t x).eval B (WordVar.val (φ := d.sortMap) (B := fun t => B t) b)).Dom :=
  fun _ _ => trivial

lemma holdsAll_domWord (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)
    {ws : List S} (b : (j : Fin ws.length) → B (d.sortMap (ws.get j))) :
    EEq.HoldsAll B (WordVar.val (φ := d.sortMap) (B := fun t => B t) b) (d.domWord ws) ↔
      ∀ j, EEq.HoldsAll B (WordVar.single (F := fun t => B t) (b j)) (d.dom (ws.get j)) := by
  have key : ∀ j, (fun t x => ((d.iota j t x).eval B
      (WordVar.val (φ := d.sortMap) (B := fun t => B t) b)).get (d.iota_eval B b j t x)) =
        WordVar.single (F := fun t => B t) (b j) := fun j => by
    funext t x
    unfold WordVar.single
    generalize hx : x.single_eq = h
    subst h
    rfl
  simp only [domWord, EEq.HoldsAll, Set.mem_iUnion, forall_exists_index]
  rw [forall_comm]
  refine forall_congr' fun j => ?_
  have := EEq.holdsAll_subst B (d.iota j) _ (d.iota_eval B b j) (d.dom (ws.get j))
  rw [key j] at this
  exact this
```

The draft states that $`\Delta_{(\varphi, D)}` is a functor from $`\mathsf{PAlg}(\Lambda)` to
$`\mathsf{Set}^S`; the library states its functoriality as identities between $`S`-sorted
mappings.

:::proposition (label := "gen-ep-derivor.delta-functor") (central := false) (title := "The functor of domains")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor. Then
$`\Delta_{(\varphi, D)}` preserves identities and composites. Moreover, a family
$`\mathbf{b} \in B_{\varphi^{\star}(\mathbf{s})}` is in $`(B_{(\varphi, D)})_{\mathbf{s}}` if
and only if $`\mathbf{B} \models D_{\mathbf{s}}[\mathbf{b}]`, and, if every $`D_s` is empty,
then $`(B_{(\varphi, D)})_s` is the whole of $`B_{\varphi(s)}`.

```lean
theorem deltaMap_id (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig) :
    d.deltaMap (PartialAlgebra.Hom.id B) = fun _ b => b := rfl

theorem deltaMap_comp (d : GenEpDerivor Sg Lg) {B B' B'' : PartialAlgebra.{u', v', w} Lg.sig}
    (g : PartialAlgebra.Hom B' B'') (f : PartialAlgebra.Hom B B') :
    d.deltaMap (g.comp f) = fun s b => d.deltaMap g s (d.deltaMap f s b) := rfl

theorem holdsAll_domWord_iff (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)
    {ws : List S} (b : (j : Fin ws.length) → B (d.sortMap (ws.get j))) :
    EEq.HoldsAll B (WordVar.val (φ := d.sortMap) (B := fun t => B t) b) (d.domWord ws) ↔
      ∀ j, ∃ b' : d.domCarrier B (ws.get j), b'.1 = b j :=
  (d.holdsAll_domWord B b).trans
    ⟨fun h j => ⟨⟨b j, h j⟩, rfl⟩, fun h j => by obtain ⟨b', hb'⟩ := h j; exact hb' ▸ b'.2⟩

theorem domCarrier_of_empty (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)
    (h : ∀ s, d.dom s = ∅) (s : S) (b : B (d.sortMap s)) :
    EEq.HoldsAll B (WordVar.single (F := fun t => B t) b) (d.dom s) := by
  rw [h s]
  exact fun _ he => he.elim
```
:::

:::proof (of := "gen-ep-derivor.delta-functor")
Restrictions preserve identities and composites. Since $`\iota^{\mathbf{s}}_j` only renames a
variable, $`\mathbf{B} \models (\iota^{\mathbf{s}}_j)^{\sharp}[D_{s_j}][\mathbf{b}]` if and
only if $`\mathbf{B} \models D_{s_j}[b_j]`, by Corollary {name}`EEq.holdsAll_subst`. If
$`D_s = \varnothing`, there is nothing to satisfy.
:::

# Domains and translations

To translate an existence equation along $`\mathbf{d}`, it does not suffice to apply
$`d^{\sharp}` to both sides: if $`d(\sigma)` does not contain the variable
$`v^{\mathbf{s}}_j`, then $`d^{\sharp}(\sigma((P_i)_i))` can be defined although $`P_j` is not.
The translation therefore also states that every subterm is defined, and this requires the
domains of the operation symbols, which in turn are given by the translations of their domain
conditions. Both are defined at once by recursion along $`\lhd`.

In Lean, the definedness conditions and the translations are first defined for an arbitrary
assignment $`\delta` of sets of equations to the operation symbols, and for terms with
arbitrary variables translated along a mapping $`\rho`, as in
Definition {name}`Derivor.trans`. The domain $`\mathrm{Dom}_{\mathbf{d}}(\sigma)` is then
defined by well-founded recursion along $`\lhd`: at $`\sigma`, the assignment used is the
domain of the symbols $`\tau \lhd \sigma`, already defined, and $`\varnothing` elsewhere. Only
the symbols that occur in $`\mathrm{def}^{\mathbf{\Sigma}}(\sigma)`, which precede $`\sigma`,
are consulted, so that the result satisfies the equation of the draft, proved below.

:::definition (label := "gen-ep-derivor.dom-tr") (central := false) (title := "Domains of operation symbols and translations")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}`. By recursion along $`\lhd`, we define, for every
$`\sigma \in \Sigma_{\mathbf{s}, s}`, the *domain of $`\sigma` along $`\mathbf{d}`*,
$`\mathrm{Dom}_{\mathbf{d}}(\sigma) \subseteq \mathrm{Eq}_{\Lambda}(\downarrow\varphi^{\star}(\mathbf{s}))`,
together with the *definedness conditions* $`\mathrm{dfd}_{\mathbf{d}}(R)` of the terms and the
*translations* of the existence equations:

1. $`\mathrm{dfd}_{\mathbf{d}}(x) = \varnothing` for a variable, and
   $`\mathrm{dfd}_{\mathbf{d}}(\tau((R_j)_j)) = \bigcup_j \mathrm{dfd}_{\mathbf{d}}(R_j) \cup (d^{\sharp}(R_j))^{\sharp}_j[\mathrm{Dom}_{\mathbf{d}}(\tau)]`;
2. $`\mathrm{tr}_{\mathbf{d}}(P, Q) = \{(d^{\sharp}(P), d^{\sharp}(Q))\} \cup \mathrm{dfd}_{\mathbf{d}}(P) \cup \mathrm{dfd}_{\mathbf{d}}(Q)`,
   and $`\mathrm{tr}_{\mathbf{d}}[\mathcal{H}]` is the union of the translations of the
   equations of $`\mathcal{H}`;
3. $`\mathrm{Dom}_{\mathbf{d}}(\sigma) = D_{\mathbf{s}} \cup \mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)] \cup \{(d(\sigma), d(\sigma))\} \cup d(\sigma)^{\sharp}[D_s]`,
   where $`d(\sigma)^{\sharp}` substitutes $`d(\sigma)` for the single variable.

```lean
/-- An assignment of sets of equations to the operation symbols. -/
abbrev DomAssign (d : GenEpDerivor Sg Lg) : Type _ :=
  ∀ σ : Sg.sig.Symbol, Set (EEq Lg.sig (WordVar d.sortMap σ.1))

/-- The substitution `(d♯(R_j))♯_j`. -/
def argSubst (d : GenEpDerivor Sg Lg) {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lg.sig Y (d.sortMap s)) {ws : List S}
    (ts : (j : Fin ws.length) → Term Sg.sig X (ws.get j)) :
    ∀ t, WordVar d.sortMap ws t → Term Lg.sig Y t :=
  fun _ v => v.2 ▸ d.trans ρ (ts v.1)

def dfd (d : GenEpDerivor Sg Lg) (δ : d.DomAssign) {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lg.sig Y (d.sortMap s)) : {s : S} → Term Sg.sig X s → Set (EEq Lg.sig Y)
  | _, .var _ => ∅
  | _, .app σ ts => (⋃ j, d.dfd δ ρ (ts j)) ∪ EEq.subst (d.argSubst ρ ts) '' δ ⟨_, _, σ⟩

def tr (d : GenEpDerivor Sg Lg) (δ : d.DomAssign) {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lg.sig Y (d.sortMap s)) (e : EEq Sg.sig X) : Set (EEq Lg.sig Y) :=
  insert ⟨_, d.trans ρ e.lhs, d.trans ρ e.rhs⟩ (d.dfd δ ρ e.lhs ∪ d.dfd δ ρ e.rhs)

def trSet (d : GenEpDerivor Sg Lg) (δ : d.DomAssign) {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lg.sig Y (d.sortMap s)) (H : Set (EEq Sg.sig X)) :
    Set (EEq Lg.sig Y) :=
  ⋃ e ∈ H, d.tr δ ρ e

/-- The right-hand side of item 3, for an assignment `δ` of domains. -/
def domStep (d : GenEpDerivor Sg Lg) (δ : d.DomAssign) (σ : Sg.sig.Symbol) :
    Set (EEq Lg.sig (WordVar d.sortMap σ.1)) :=
  d.domWord σ.1 ∪ d.trSet δ d.wordVar (Sg.defn σ.2.2) ∪ {EEq.defined (d.op σ.2.2)} ∪
    EEq.subst (WordVar.single (F := fun t => Term Lg.sig (WordVar d.sortMap σ.1) t) (d.op σ.2.2))
      '' d.dom σ.2.1

open Classical in
def Dom (d : GenEpDerivor Sg Lg) : d.DomAssign :=
  Sg.wf.fix fun σ ih =>
    d.domStep (fun τ => if h : Signature.DefPrec Sg.defn τ σ then ih τ h else ∅) σ
```
:::

```lean
lemma dfd_congr (d : GenEpDerivor Sg Lg) {δ δ' : d.DomAssign} {X : S → Type*} {Y : T → Type*}
    (ρ : ∀ s, X s → Term Lg.sig Y (d.sortMap s)) {s : S} (R : Term Sg.sig X s)
    (h : ∀ τ ∈ R.symbols, δ τ = δ' τ) : d.dfd δ ρ R = d.dfd δ' ρ R := by
  induction R with
  | var x => rfl
  | app σ ts ih =>
    simp only [dfd]
    rw [h ⟨_, _, σ⟩ (Set.mem_insert _ _)]
    congr 1
    congr 1
    funext j
    refine ih j fun τ hτ => h τ ?_
    exact Set.mem_insert_of_mem _ (Set.mem_iUnion.2 ⟨j, hτ⟩)

/-- `domStep δ σ` only depends on the domains of the symbols before `σ`. -/
lemma domStep_congr (d : GenEpDerivor Sg Lg) {δ δ' : d.DomAssign} (σ : Sg.sig.Symbol)
    (h : ∀ τ, Signature.DefPrec Sg.defn τ σ → δ τ = δ' τ) : d.domStep δ σ = d.domStep δ' σ := by
  have key : ∀ e ∈ Sg.defn σ.2.2, d.tr δ d.wordVar e = d.tr δ' d.wordVar e := fun e he => by
    unfold tr
    rw [d.dfd_congr _ e.lhs fun τ hτ => h τ ⟨e, he, Or.inl hτ⟩,
      d.dfd_congr _ e.rhs fun τ hτ => h τ ⟨e, he, Or.inr hτ⟩]
  unfold domStep trSet
  congr 4
  funext e
  congr 1
  funext he
  exact key e he
```

:::proposition (label := "gen-ep-derivor.dom-eq") (central := false) (title := "The equation of the domains")
For every operation symbol $`\sigma`,
$`\mathrm{Dom}_{\mathbf{d}}(\sigma) = D_{\mathbf{s}} \cup \mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)] \cup \{(d(\sigma), d(\sigma))\} \cup d(\sigma)^{\sharp}[D_s]`,
where the translation is taken along $`\mathrm{Dom}_{\mathbf{d}}` itself.

```lean
theorem Dom_eq (d : GenEpDerivor Sg Lg) (σ : Sg.sig.Symbol) :
    d.Dom σ = d.domStep d.Dom σ := by
  rw [Dom, WellFounded.fix_eq]
  refine d.domStep_congr σ fun τ hτ => ?_
  simp only [hτ, ↓reduceDIte]
```
:::

:::proof (of := "gen-ep-derivor.dom-eq")
By the equation of well-founded recursion, $`\mathrm{Dom}_{\mathbf{d}}(\sigma)` is item 3
computed along the assignment that agrees with $`\mathrm{Dom}_{\mathbf{d}}` on the symbols
$`\tau \lhd \sigma` and is empty elsewhere. The definedness conditions of a term only depend on
the domains of the symbols that occur in it, and the symbols that occur in
$`\mathrm{def}^{\mathbf{\Sigma}}(\sigma)` are exactly those $`\tau \lhd \sigma`.
:::

```lean
section Derived

variable (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)

lemma mem_Dom_defined {ws : List S} {s : S} (σ : Sg.sig ws s) :
    EEq.defined (d.op σ) ∈ d.Dom ⟨ws, s, σ⟩ := by
  rw [Dom_eq]
  exact Or.inl (Or.inr rfl)

lemma subst_dom_subset_Dom {ws : List S} {s : S} (σ : Sg.sig ws s) :
    EEq.subst (WordVar.single (F := fun t => Term Lg.sig (WordVar d.sortMap ws) t) (d.op σ)) ''
      d.dom s ⊆ d.Dom ⟨ws, s, σ⟩ := by
  rw [Dom_eq]
  exact Set.subset_union_right

variable {d B}

lemma eval_op_dom {ws : List S} {s : S} {σ : Sg.sig ws s}
    {c : ∀ t, WordVar d.sortMap ws t → B t} (h : EEq.HoldsAll B c (d.Dom ⟨ws, s, σ⟩)) :
    ((d.op σ).eval B c).Dom :=
  (h _ (d.mem_Dom_defined σ)).1

lemma holdsAll_dom_eval_op {ws : List S} {s : S} {σ : Sg.sig ws s}
    {c : ∀ t, WordVar d.sortMap ws t → B t} (h : EEq.HoldsAll B c (d.Dom ⟨ws, s, σ⟩))
    (hd : ((d.op σ).eval B c).Dom) :
    EEq.HoldsAll B (WordVar.single (F := fun t => B t) (((d.op σ).eval B c).get hd))
      (d.dom s) := by
  have := (EEq.holdsAll_subst B _ c (eval_single B c (d.op σ) hd) (d.dom s)).1
    fun e he => h e (d.subst_dom_subset_Dom σ he)
  rwa [eval_single_get] at this

end Derived
```

# The derived partial algebra

:::definition (label := "gen-ep-derivor.derived") (central := false) (title := "The derived partial algebra")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}` and $`\mathbf{B} = (B, G)` a partial $`\Lambda`-algebra. Then
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) = (B_{(\varphi, D)}, G^{\mathbf{d}})`, where,
for $`\sigma \in \Sigma_{\mathbf{s}, s}`, $`G^{\mathbf{d}}_{\sigma}` is the partial mapping
from $`(B_{(\varphi, D)})_{\mathbf{s}}` to $`(B_{(\varphi, D)})_s` defined at the families
$`\mathbf{b}` with $`\mathbf{B} \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[\mathbf{b}]`, where
it sends $`\mathbf{b}` to $`d(\sigma)^{\mathbf{B}}[\mathbf{b}]`. This value is defined and lies
in $`(B_{(\varphi, D)})_s`, because $`\mathrm{Dom}_{\mathbf{d}}(\sigma)` contains
$`(d(\sigma), d(\sigma))` and $`d(\sigma)^{\sharp}[D_s]`.

```lean
def derived (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig) :
    PartialAlgebra.{u, v, w} Sg.sig where
  carrier := d.domCarrier B
  op {ws s} σ b :=
    ⟨EEq.HoldsAll B (WordVar.val (φ := d.sortMap) (B := fun t => B t) fun j => (b j).1)
        (d.Dom ⟨ws, s, σ⟩),
      fun h => ⟨((d.op σ).eval B _).get (eval_op_dom h), holdsAll_dom_eval_op h _⟩⟩

/-- The values in `B` of the elements of a family of `𝐝*(B)`. -/
abbrev famVal (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig} {ws : List S}
    (b : Arity (d.derived B) ws) : ∀ t, WordVar d.sortMap ws t → B t :=
  WordVar.val (φ := d.sortMap) (B := fun t => B t) fun j => (b j).1
```
:::

The translation lemma is proved for terms with arbitrary variables $`X`, translated along a
mapping $`\rho` whose images take, in $`\mathbf{B}`, the values of the variables in
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`. The statement of the draft, for the variables
$`\downarrow\mathbf{s}` and a family $`\mathbf{b} \in (B_{(\varphi, D)})_{\mathbf{s}}`, is the
case of $`d^{\sharp}`.

:::Stemma.lemma (label := "gen-ep-derivor.translation") (central := false) (title := "Translation")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}`,
$`\mathbf{B}` a partial $`\Lambda`-algebra, $`\mathbf{s} \in S^{\star}` and
$`\mathbf{b} \in (B_{(\varphi, D)})_{\mathbf{s}}`. Then, for every term
$`R \in \mathrm{T}_{\Sigma}(\downarrow\mathbf{s})_t`,
$`R^{\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})}[\mathbf{b}]` is defined if and only if
$`\mathbf{B} \models \mathrm{dfd}_{\mathbf{d}}(R)[\mathbf{b}]`, and then it is
$`d^{\sharp}(R)^{\mathbf{B}}[\mathbf{b}]`. Consequently, for every
$`\mathcal{H} \subseteq \mathrm{Eq}_{\Sigma}(\downarrow\mathbf{s})`,
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathcal{H}[\mathbf{b}]` if and only if
$`\mathbf{B} \models \mathrm{tr}_{\mathbf{d}}[\mathcal{H}][\mathbf{b}]`. The same holds for
terms with variables in any $`X`, translated along any $`\rho` with
$`\rho(x)^{\mathbf{B}}[c] = a(x)` for every $`x`, in place of $`d^{\sharp}` and $`\mathbf{b}`.

```lean
theorem eval_derived (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)
    {X : S → Type*} {Y : T → Type*} (ρ : ∀ s, X s → Term Lg.sig Y (d.sortMap s))
    (c : ∀ t, Y t → B t) (a : ∀ s, X s → d.derived B s)
    (hρ : ∀ s x, (a s x).1 ∈ (ρ s x).eval B c) {s : S} (R : Term Sg.sig X s) :
    ((R.eval (d.derived B) a).Dom ↔ EEq.HoldsAll B c (d.dfd d.Dom ρ R)) ∧
      ∀ h, ((R.eval (d.derived B) a).get h).1 ∈ (d.trans ρ R).eval B c := by
  induction R with
  | var x => exact ⟨⟨fun _ _ he => he.elim, fun _ => trivial⟩, fun _ => hρ _ x⟩
  | @app ws s σ ts ih =>
    -- Once the arguments are defined, so are their translations, with the same values.
    have hf : ∀ (hts : ∀ j, ((ts j).eval (d.derived B) a).Dom) t v,
        ((d.argSubst ρ ts t v).eval B c).Dom := fun hts t v => by
      obtain ⟨j, hj⟩ := v
      subst hj
      exact Part.dom_iff_mem.2 ⟨_, (ih j).2 (hts j)⟩
    have hval : ∀ hts : ∀ j, ((ts j).eval (d.derived B) a).Dom,
        (fun t v => ((d.argSubst ρ ts t v).eval B c).get (hf hts t v)) =
          WordVar.val (φ := d.sortMap) (B := fun t => B t)
            fun j => (((ts j).eval (d.derived B) a).get (hts j)).1 := fun hts => by
      funext t v
      obtain ⟨j, hj⟩ := v
      subst hj
      exact Part.get_eq_of_mem ((ih j).2 (hts j)) _
    have hsub : ∀ hts : ∀ j, ((ts j).eval (d.derived B) a).Dom,
        EEq.HoldsAll B c (EEq.subst (d.argSubst ρ ts) '' d.Dom ⟨ws, s, σ⟩) ↔
          ((d.derived B).op σ fun j => ((ts j).eval (d.derived B) a).get (hts j)).Dom :=
      fun hts => by
        rw [EEq.holdsAll_subst B _ c (hf hts), hval hts]
        rfl
    refine ⟨⟨fun ⟨hts, hop⟩ => ?_, fun h => ?_⟩, fun ⟨hts, hop⟩ => ?_⟩
    · exact holdsAll_union.2 ⟨holdsAll_iUnion.2 fun j => ((ih j).1.1 (hts j)), (hsub hts).2 hop⟩
    · obtain ⟨h₁, h₂⟩ := holdsAll_union.1 h
      have hts : ∀ j, ((ts j).eval (d.derived B) a).Dom := fun j =>
        (ih j).1.2 (holdsAll_iUnion.1 h₁ j)
      exact ⟨hts, (hsub hts).1 h₂⟩
    · change ((d.op σ).eval B _).get _ ∈ ((d.op σ).subst (d.argSubst ρ ts)).eval B c
      rw [Term.eval_subst B _ c (hf hts), hval hts]
      exact Part.get_mem _

theorem holdsAll_derived (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)
    {X : S → Type*} {Y : T → Type*} (ρ : ∀ s, X s → Term Lg.sig Y (d.sortMap s))
    (c : ∀ t, Y t → B t) (a : ∀ s, X s → d.derived B s)
    (hρ : ∀ s x, (a s x).1 ∈ (ρ s x).eval B c) (H : Set (EEq Sg.sig X)) :
    EEq.HoldsAll (d.derived B) a H ↔ EEq.HoldsAll B c (d.trSet d.Dom ρ H) := by
  have key : ∀ e : EEq Sg.sig X,
      e.Holds (d.derived B) a ↔ EEq.HoldsAll B c (d.tr d.Dom ρ e) := by
    intro e
    have hl := d.eval_derived B ρ c a hρ e.lhs
    have hr := d.eval_derived B ρ c a hρ e.rhs
    simp only [tr, EEq.HoldsAll, Set.mem_insert_iff, forall_eq_or_imp]
    change _ ↔ _ ∧ EEq.HoldsAll B c _
    rw [holdsAll_union, ← hl.1, ← hr.1]
    constructor
    · rintro ⟨h₁, h₂, he⟩
      refine ⟨(EEq.holds_iff_mem B c _).2 ⟨_, hl.2 h₁, ?_⟩, h₁, h₂⟩
      rw [he]
      exact hr.2 h₂
    · rintro ⟨hh, h₁, h₂⟩
      obtain ⟨x, m₁, m₂⟩ := (EEq.holds_iff_mem B c _).1 hh
      exact ⟨h₁, h₂, Subtype.ext ((Part.mem_unique (hl.2 h₁) m₁).trans
        (Part.mem_unique (hr.2 h₂) m₂).symm)⟩
  exact ⟨fun h e' he' => by
      obtain ⟨e, he'⟩ := Set.mem_iUnion.1 he'
      obtain ⟨he, he'⟩ := Set.mem_iUnion.1 he'
      exact (key e).1 (h e he) e' he',
    fun h e he => (key e).2 fun e' he' =>
      h e' (Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨he, he'⟩⟩)⟩

lemma wordVar_mem (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig}
    {ws : List S} (b : Arity (d.derived B) ws) :
    ∀ s x, (b.val s x).1 ∈ (d.wordVar s x).eval B (d.famVal b) := by
  rintro s ⟨j, h⟩
  subst h
  exact Part.mem_some _

theorem translation (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)
    {ws : List S} (b : Arity (d.derived B) ws) {s : S} (R : Term Sg.sig (WordVar id ws) s) :
    ((R.eval (d.derived B) b.val).Dom ↔
        EEq.HoldsAll B (d.famVal b) (d.dfd d.Dom d.wordVar R)) ∧
      ∀ h, ((R.eval (d.derived B) b.val).get h).1 ∈ (d.sharp R).eval B (d.famVal b) :=
  d.eval_derived B _ _ _ (d.wordVar_mem b) R

theorem holdsAll_translation (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)
    {ws : List S} (b : Arity (d.derived B) ws) (H : Set (EEq Sg.sig (WordVar id ws))) :
    EEq.HoldsAll (d.derived B) b.val H ↔
      EEq.HoldsAll B (d.famVal b) (d.trSet d.Dom d.wordVar H) :=
  d.holdsAll_derived B _ _ _ (d.wordVar_mem b) H
```
:::

:::proof (of := "gen-ep-derivor.translation")
By induction on $`R`. For a variable $`x`, there are no definedness conditions, and the value
of $`x` is $`a(x)`, which is the value of $`\rho(x)`. Let $`R = \sigma((R_j)_j)`; its
translation is $`d(\sigma)` with the translations of the $`R_j` substituted. The term $`R` is
defined in $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` if and only if every $`R_j` is
defined, that is, by the induction hypothesis, $`\mathbf{B}` satisfies their definedness
conditions, and the family $`\mathbf{c}` of their values is in the domain of
$`G^{\mathbf{d}}_{\sigma}`, that is, $`\mathbf{B} \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[\mathbf{c}]`.
Since the values $`c_j` are those of the translations of the $`R_j`, by
Corollary {name}`EEq.holdsAll_subst` the latter holds if and only if
$`\mathbf{B} \models (d^{\sharp}(R_j))^{\sharp}_j[\mathrm{Dom}_{\mathbf{d}}(\sigma)]`, and,
by Lemma {name}`Term.eval_subst`, the value of $`R`, $`d(\sigma)^{\mathbf{B}}[\mathbf{c}]`, is
that of its translation. An existence equation $`(P, Q)` then holds in
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` if and only if $`P` and $`Q` are defined there,
that is, $`\mathbf{B}` satisfies their definedness conditions, and their values, those of the
translations of $`P` and $`Q`, are equal.
:::

:::proposition (label := "gen-ep-derivor.domain-def") (central := false) (title := "The domains of the derived operations")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}`,
$`\mathbf{B}` a partial $`\Lambda`-algebra, $`\sigma \in \Sigma_{\mathbf{s}, s}` and
$`\mathbf{b} \in (B_{(\varphi, D)})_{\mathbf{s}}`. Then $`\mathbf{b}` is in the domain of
$`\sigma` in $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` if and only if
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{b}]`,
$`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` is defined and
$`d(\sigma)^{\mathbf{B}}[\mathbf{b}] \in (B_{(\varphi, D)})_s`. Consequently,
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is a $`\mathbf{\Sigma}`-algebra if and only
if, for every $`\sigma` and every $`\mathbf{b}` with
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{b}]`,
$`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` is defined and is in $`(B_{(\varphi, D)})_s`.

```lean
theorem derived_op_dom (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig)
    {ws : List S} {s : S} (σ : Sg.sig ws s) (b : Arity (d.derived B) ws) :
    ((d.derived B).op σ b).Dom ↔ EEq.HoldsAll (d.derived B) b.val (Sg.defn σ) ∧
      ∃ h : ((d.op σ).eval B (d.famVal b)).Dom,
        EEq.HoldsAll B (WordVar.single (F := fun t => B t) (((d.op σ).eval B _).get h))
          (d.dom s) := by
  change EEq.HoldsAll B (d.famVal b) (d.Dom ⟨ws, s, σ⟩) ↔ _
  rw [Dom_eq, holdsAll_translation]
  unfold domStep
  simp only [holdsAll_union]
  have hw : EEq.HoldsAll B (d.famVal b) (d.domWord ws) :=
    (d.holdsAll_domWord B _).2 fun j => (b j).2
  have hdef : EEq.HoldsAll B (d.famVal b) {EEq.defined (d.op σ)} ↔
      ((d.op σ).eval B (d.famVal b)).Dom :=
    ⟨fun h => (h _ rfl).1, fun h e he => by subst he; exact ⟨h, h, rfl⟩⟩
  rw [hdef]
  constructor
  · rintro ⟨⟨⟨-, ht⟩, hd⟩, hD⟩
    refine ⟨ht, hd, ?_⟩
    have := (EEq.holdsAll_subst B _ _ (eval_single B _ (d.op σ) hd) (d.dom s)).1 hD
    rwa [eval_single_get] at this
  · rintro ⟨ht, hd, hD⟩
    refine ⟨⟨⟨hw, ht⟩, hd⟩, ?_⟩
    rw [EEq.holdsAll_subst B _ _ (eval_single B _ (d.op σ) hd), eval_single_get]
    exact hD

theorem isAlgebra_derived_iff (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig) :
    Sg.IsAlgebra (d.derived B) ↔
      ∀ {ws : List S} {s : S} (σ : Sg.sig ws s) (b : Arity (d.derived B) ws),
        EEq.HoldsAll (d.derived B) b.val (Sg.defn σ) →
          ∃ h : ((d.op σ).eval B (d.famVal b)).Dom,
            EEq.HoldsAll B (WordVar.single (F := fun t => B t) (((d.op σ).eval B _).get h))
              (d.dom s) := by
  constructor
  · intro h ws s σ b hb
    exact ((d.derived_op_dom B σ b).1 ((h σ b).2 hb)).2
  · intro h ws s σ b
    rw [d.derived_op_dom B σ b]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', h σ b h'⟩⟩
```
:::

:::proof (of := "gen-ep-derivor.domain-def")
By Proposition {name}`GenEpDerivor.Dom_eq`, $`\mathbf{B} \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[\mathbf{b}]`
splits into four conditions. The first, $`\mathbf{B} \models D_{\mathbf{s}}[\mathbf{b}]`, holds
because $`\mathbf{b}` is a family of $`B_{(\varphi, D)}`. By Lemma {name}`GenEpDerivor.translation`,
the second is $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{b}]`.
The third says that $`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` is defined, and then, by
Corollary {name}`EEq.holdsAll_subst`, the fourth says that its value satisfies $`D_s`. The
second statement follows: $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is a
$`\mathbf{\Sigma}`-algebra when its domains are exactly the families satisfying the domain
conditions, and they are always contained in them.
:::

Thus $`\sigma` is interpreted in $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` as the
restriction of the derived operation $`d(\sigma)^{\mathbf{B}}` to the families of the domains
that satisfy the domain conditions of $`\sigma` and on which it takes a value in the domain of
$`s`.

# The functor

:::proposition (label := "gen-ep-derivor.functor") (central := false) (title := "The functor of a generalized ep-derivor")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}`. Then $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` is a functor from
$`\mathsf{PAlg}(\Lambda)` to $`\mathsf{PAlg}(\Sigma)`: it sends $`\mathbf{B}` to
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` and a homomorphism $`f` to
$`\Delta_{(\varphi, D)}(f)`, which is a homomorphism. Forgetting the operations of
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}` gives $`\Delta_{(\varphi, D)}`.

```lean
def derivedMap (d : GenEpDerivor Sg Lg) {B B' : PartialAlgebra.{u', v', w} Lg.sig}
    (f : PartialAlgebra.Hom B B') : PartialAlgebra.Hom (d.derived B) (d.derived B') where
  map := d.deltaMap f
  map_dom {ws s} σ b h := by
    have := EEq.holdsAll_hom f (d.famVal b) h
    rwa [wordVar_val_map (G := fun t => B' t)] at this
  map_op {ws s} σ b h := by
    apply Subtype.ext
    change f.map _ (((d.op σ).eval B _).get _) = ((d.op σ).eval B' _).get _
    obtain ⟨hB, e⟩ := Term.eval_hom f (d.famVal b) (d.op σ) (eval_op_dom h)
    rw [← e]
    exact Part.get_eq_get_of_eq _ _ (congrArg (fun c => (d.op σ).eval B' c)
      (wordVar_val_map (G := fun t => B' t) f.map fun j => (b j).1))

def functor (d : GenEpDerivor Sg Lg) :
    PartialAlgebra.{u', v', w} Lg.sig ⥤ PartialAlgebra.{u, v, w} Sg.sig where
  obj := d.derived
  map f := d.derivedMap f
  map_id _ := rfl
  map_comp _ _ := rfl

theorem functor_obj_carrier (d : GenEpDerivor Sg Lg) (B : PartialAlgebra.{u', v', w} Lg.sig) :
    (d.functor.obj B).carrier = d.domCarrier B := rfl

theorem functor_map_map (d : GenEpDerivor Sg Lg) {B B' : PartialAlgebra.{u', v', w} Lg.sig}
    (f : B ⟶ B') : (d.functor.map f).map = d.deltaMap f := rfl
```
:::

:::proof (of := "gen-ep-derivor.functor")
Let $`f \colon \mathbf{B} \to \mathbf{B}'` be a homomorphism and $`\mathbf{b}` in the domain of
$`G^{\mathbf{d}}_{\sigma}`, that is, $`\mathbf{B} \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[\mathbf{b}]`.
By Corollary {name}`EEq.holdsAll_hom`, $`\mathbf{B}' \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[f \circ \mathbf{b}]`,
and, by Lemma {name}`Term.eval_hom`, $`d(\sigma)^{\mathbf{B}'}[f \circ \mathbf{b}] = f(d(\sigma)^{\mathbf{B}}[\mathbf{b}])`.
Hence $`\Delta_{(\varphi, D)}(f)` is a homomorphism. It preserves identities and composites by
Proposition {name}`GenEpDerivor.deltaMap_id`, and the carrier of
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is $`B_{(\varphi, D)}` by definition.
:::

# Closed subsets and congruences

:::proposition (label := "gen-ep-derivor.closed-congruence") (central := false) (title := "Closed subsets and congruences of the derived algebra")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}` and $`\mathbf{B}` a partial $`\Lambda`-algebra.

1. If $`Y` is a closed subset of $`\mathbf{B}`, then
   $`Y_{\varphi} \cap B_{(\varphi, D)} = (Y_{\varphi(s)} \cap (B_{(\varphi, D)})_s)_{s \in S}`
   is a closed subset of $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`.
2. If $`\Phi` is a congruence on $`\mathbf{B}`, then
   $`\Phi_{\varphi} \cap (B_{(\varphi, D)} \times B_{(\varphi, D)})` is a congruence on
   $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`.

```lean
theorem isClosed_derived (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig}
    {Y : ∀ t, Set (B t)} (hY : B.IsClosed Y) :
    (d.derived B).IsClosed fun s => {b | b.1 ∈ Y (d.sortMap s)} := by
  intro ws s σ b hb h
  refine Term.eval_mem_closed hY _ ?_ (d.op σ) _
  rintro t ⟨j, hj⟩
  subst hj
  exact hb j

theorem isCongruence_derived (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig}
    {Φ : ∀ t, B t → B t → Prop} (hΦ : B.IsCongruence Φ) :
    (d.derived B).IsCongruence fun s b b' => Φ (d.sortMap s) b.1 b'.1 where
  equivalence s :=
    ⟨fun b => (hΦ.equivalence _).refl b.1, fun h => (hΦ.equivalence _).symm h,
      fun h h' => (hΦ.equivalence _).trans h h'⟩
  compat σ a b hab ha hb := by
    refine Term.eval_congruence hΦ _ _ ?_ (d.op σ) _ _
    rintro t ⟨j, hj⟩
    subst hj
    exact hab j
```
:::

:::proof (of := "gen-ep-derivor.closed-congruence")
In both cases the operation $`G^{\mathbf{d}}_{\sigma}` is the value of the term $`d(\sigma)` in
$`\mathbf{B}` where defined, so Lemma {name}`Term.eval_mem_closed` applies. (1) If
$`\mathbf{y}` is a family of $`Y_{\varphi} \cap B_{(\varphi, D)}` in the domain of
$`G^{\mathbf{d}}_{\sigma}`, then $`d(\sigma)^{\mathbf{B}}[\mathbf{y}] \in Y_{\varphi(s)}`, and
it is in $`(B_{(\varphi, D)})_s` because it is a value of $`G^{\mathbf{d}}_{\sigma}`. (2) The
restriction of an equivalence is an equivalence; if $`\mathbf{a}` and $`\mathbf{b}` are in the
domain of $`G^{\mathbf{d}}_{\sigma}` and are related letter by letter, then
$`d(\sigma)^{\mathbf{B}}[\mathbf{a}]` and $`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` are defined and
$`\Phi_{\varphi(s)}`-related.
:::

```lean
end GenEpDerivor

end CategorialAlgebras
```
