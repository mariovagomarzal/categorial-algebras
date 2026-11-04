import Mathlib.CategoryTheory.Category.Basic
import CategorialAlgebras.Evaluation

/-!
# Substitutions and derivors

This file gathers the notions on terms that the generalized ep-derivors of Section
`SGenEpDerivors` of the draft rest on: the variables of a word, substitutions, the values of
terms under substitutions and homomorphisms, and the derivors between many-sorted signatures,
with the category $\mathsf{Sig}_{\mathfrak{d}}$ they form.
-/

universe u v u' v' u'' v'' w

namespace CategorialAlgebras

open Signature

variable {S : Type u} {Sig : Signature.{u, v} S}

/-!
## The variables of a word

The draft fixes the variables $v^{s}_{n}$, for $s \in S$ and $n \in \mathbb{N}$, and lets
$\downarrow\mathbf{s}$ be the variables $v^{s}_{i}$ for $i$ smaller than the number of
occurrences of $s$ in the word $\mathbf{s}$; it then identifies the $j$-th letter of
$\mathbf{s}$ with a variable $v^{\mathbf{s}}_{j}$, and a family $\mathbf{a} \in A_{\mathbf{s}}$
with the valuation that sends $v^{\mathbf{s}}_{j}$ to $a_j$. The library takes this
identification as the definition: the variables of $\mathbf{s}$ *are* its positions, the
position $j$ being a variable of sort $s_j$.
-/

/-!
### Variables of a word

For a set $I$ and a mapping $\kappa \colon I \to S$, the $S$-sorted set of *variables*
$\downarrow\kappa$ has, as variables of sort $s$, the $i \in I$ with $\kappa(i) = s$. For a
word $\mathbf{s}$, $\downarrow\mathbf{s}$ is $\downarrow\kappa$ for the mapping
$j \mapsto s_j$ on $|\mathbf{s}|$; for a mapping $\varphi \colon S \to T$,
$\downarrow\varphi^{\star}(\mathbf{s})$ is $\downarrow\kappa$ for $j \mapsto \varphi(s_j)$.
A family $\mathbf{a} = (a_i)_{i \in I}$ with $a_i \in A_{\kappa(i)}$ is identified with the
valuation of $\downarrow\kappa$ in $A$ that sends $i$ to $a_i$.
-/

/-- The variables indexed by `I`, the variable `i` being of sort `κ i`. -/
def Vars {I : Type} (κ : I → S) : S → Type := fun s => {i : I // κ i = s}

variable {I : Type} {κ : I → S}

/-- The variable `i`, of sort `κ i`. -/
def Vars.mk (i : I) : Vars κ (κ i) := ⟨i, rfl⟩

/-- The valuation of `↓κ` given by a family. -/
def famVal {A : S → Type w} (a : ∀ i, A (κ i)) : ∀ s, Vars κ s → Part (A s) :=
  fun _ x => Part.some (x.2 ▸ a x.1)

@[simp] lemma famVal_mk {A : S → Type w} (a : ∀ i, A (κ i)) (i : I) :
    famVal a (κ i) (Vars.mk i) = Part.some (a i) := rfl

/-!
## Substitutions
-/

/-!
### Substitutions

For $S$-sorted sets $X$ and $Y$ and an $S$-sorted mapping
$f \colon X \to \mathrm{T}_{\Sigma}(Y)$, the *substitution* $f^{\sharp}$ is the mapping from
$\mathrm{T}_{\Sigma}(X)$ to $\mathrm{T}_{\Sigma}(Y)$ that replaces every variable $x$ by
$f(x)$: $f^{\sharp}(x) = f(x)$ and
$f^{\sharp}(\sigma((t_j)_j)) = \sigma((f^{\sharp}(t_j))_j)$. It acts on existence equations
member by member, and $f^{\sharp}[\mathcal{H}]$ is the image of a set $\mathcal{H}$ of
existence equations. For a family $(P_i)_{i \in I}$ with $P_i \in \mathrm{T}_{\Sigma}(Y)_{\kappa(i)}$,
$(P_i)^{\sharp}_{i \in I}$ is the substitution that sends the variable $i$ of $\downarrow\kappa$
to $P_i$.
-/

/-- The substitution `f♯`. -/
def Term.subst {X Y : S → Type} (f : ∀ s, X s → Term Sig Y s) : {s : S} → Term Sig X s → Term Sig Y s
  | _, .var x => f _ x
  | _, .app σ ts => .app σ fun j => (ts j).subst f

/-- The substitution `f♯` on an existence equation. -/
def EEq.subst {X Y : S → Type} (f : ∀ s, X s → Term Sig Y s) (e : EEq Sig X) : EEq Sig Y :=
  ⟨e.sort, e.lhs.subst f, e.rhs.subst f⟩

/-- The image `f♯[ℋ]` of a set of existence equations. -/
def EEq.substSet {X Y : S → Type} (f : ∀ s, X s → Term Sig Y s) (H : Set (EEq Sig X)) :
    Set (EEq Sig Y) :=
  EEq.subst f '' H

/-- The substitution `(Pᵢ)♯` that sends the variable `i` of `↓κ` to `P i`. -/
def famSubst {Y : S → Type} (P : ∀ i, Term Sig Y (κ i)) : ∀ s, Vars κ s → Term Sig Y s :=
  fun _ x => x.2 ▸ P x.1

/-!
### Satisfaction of a set of existence equations

For a set $\mathcal{H}$ of existence equations, $\mathbf{A} \models \mathcal{H}[a]$ when every
equation of $\mathcal{H}$ holds in $\mathbf{A}$ under the valuation $a$.
-/

/-- `𝐀 ⊨ ℋ[a]`. -/
def EEq.HoldsAll {X : S → Type} (A : PartialAlgebra.{u, v, w} Sig) (val : ∀ s, X s → Part (A s))
    (H : Set (EEq Sig X)) : Prop :=
  ∀ e ∈ H, e.Holds A val

namespace Term

variable {X Y : S → Type}

lemma subst_var_of {f : ∀ s, X s → Term Sig X s} (hf : ∀ s x, f s x = .var x) :
    ∀ {t : S} (R : Term Sig X t), R.subst f = R
  | _, .var x => hf _ x
  | _, .app σ ts => by simp only [Term.subst]; congr 1; funext j; exact subst_var_of hf (ts j)

lemma subst_subst {Z : S → Type} (f : ∀ s, X s → Term Sig Y s) (g : ∀ s, Y s → Term Sig Z s) :
    ∀ {t : S} (R : Term Sig X t), (R.subst f).subst g = R.subst fun s x => (f s x).subst g
  | _, .var x => rfl
  | _, .app σ ts => by simp only [Term.subst]; congr 1; funext j; exact subst_subst f g (ts j)

/-- The value of `σ((tⱼ)ⱼ)` only depends on the values of the `tⱼ`. -/
lemma eval_app_congr {A : PartialAlgebra.{u, v, w} Sig} {val : ∀ s, X s → Part (A s)}
    {val' : ∀ s, Y s → Part (A s)} {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → Term Sig X (ws.get j)}
    {ts' : (j : Fin ws.length) → Term Sig Y (ws.get j)}
    (h : ∀ j, (ts j).eval A val = (ts' j).eval A val') :
    (Term.app σ ts).eval A val = (Term.app σ ts').eval A val' := by
  have hf : (fun j => (ts j).eval A val) = fun j => (ts' j).eval A val' := funext h
  have key : ∀ p q : (j : Fin ws.length) → Part (A (ws.get j)), p = q →
      (⟨∃ h : ∀ j, (p j).Dom, (A.op σ fun j => (p j).get (h j)).Dom,
        fun h => (A.op σ fun j => (p j).get (h.1 j)).get h.2⟩ : Part (A s)) =
      ⟨∃ h : ∀ j, (q j).Dom, (A.op σ fun j => (q j).get (h j)).Dom,
        fun h => (A.op σ fun j => (q j).get (h.1 j)).get h.2⟩ := by
    rintro p _ rfl; rfl
  exact key _ _ hf

end Term

lemma famSubst_subst {I : Type} {κ : I → S} {Y Z : S → Type} (P : ∀ i, Term Sig Y (κ i))
    (g : ∀ s, Y s → Term Sig Z s) (s : S) (x : Vars κ s) :
    (famSubst P s x).subst g = famSubst (fun i => (P i).subst g) s x := by
  obtain ⟨i, rfl⟩ := x; rfl

/-!
## Values of terms

The draft states the next fact for total valuations, with the hypothesis that every
$f(y)^{\mathbf{A}}[a]$ be defined, and observes that it cannot be dropped. Valuations are partial
in the library, and $f^{\mathbf{A}}[a]$, the valuation that sends $y$ to
$f(y)^{\mathbf{A}}[a]$, is undefined where $f(y)^{\mathbf{A}}[a]$ is; the equality then holds
with no hypothesis, and the draft's statement is the case in which $f^{\mathbf{A}}[a]$ is total.
-/

/-!
### Values under a substitution

Let $\mathbf{A}$ be a partial $\Sigma$-algebra, $f \colon X \to \mathrm{T}_{\Sigma}(Y)$ and
$a$ a valuation of $Y$ in $A$. For every term $R \in \mathrm{T}_{\Sigma}(X)_t$,
$f^{\sharp}(R)^{\mathbf{A}}[a]$ is defined if and only if $R^{\mathbf{A}}[f^{\mathbf{A}}[a]]$ is
defined, and then they are equal. Consequently, for every set $\mathcal{H}$ of existence
equations with variables in $X$, $\mathbf{A} \models f^{\sharp}[\mathcal{H}][a]$ if and only if
$\mathbf{A} \models \mathcal{H}[f^{\mathbf{A}}[a]]$.
-/

theorem Term.eval_subst {X Y : S → Type} (A : PartialAlgebra.{u, v, w} Sig)
    (f : ∀ s, X s → Term Sig Y s) (val : ∀ s, Y s → Part (A s)) {t : S} (R : Term Sig X t) :
    (R.subst f).eval A val = R.eval A (fun s x => (f s x).eval A val) := by
  induction R with
  | var x => simp [Term.subst]
  | app σ ts ih => exact Term.eval_app_congr σ ih

theorem EEq.holdsAll_substSet {X Y : S → Type} (A : PartialAlgebra.{u, v, w} Sig)
    (f : ∀ s, X s → Term Sig Y s) (val : ∀ s, Y s → Part (A s)) (H : Set (EEq Sig X)) :
    EEq.HoldsAll A val (EEq.substSet f H) ↔
      EEq.HoldsAll A (fun s x => (f s x).eval A val) H := by
  simp only [EEq.HoldsAll, EEq.substSet, Set.forall_mem_image, EEq.Holds, EEq.subst,
    Term.eval_subst]

/-!
*Proof of “Values under a substitution”.*

By induction on $R$. For a variable $x$, both sides are $f(x)^{\mathbf{A}}[a]$. For
$R = \sigma((R_j)_j)$, $f^{\sharp}(R) = \sigma((f^{\sharp}(R_j))_j)$, and both sides are defined
exactly when the values of the $R_j$, equal by the induction hypothesis, are defined and in the
domain of $F_\sigma$, and then both are the value of $F_\sigma$ on them. The second statement
follows, an existence equation holding exactly when the values of its members are defined and
equal.
-/

/-!
### Values under a homomorphism

Let $h \colon \mathbf{A} \to \mathbf{B}$ be a homomorphism of partial $\Sigma$-algebras and
$a$ a valuation of $X$ in $A$. If $P^{\mathbf{A}}[a]$ is defined, then
$P^{\mathbf{B}}[h \circ a]$ is defined and equal to $h(P^{\mathbf{A}}[a])$. Consequently, if
$\mathbf{A} \models \mathcal{H}[a]$, then $\mathbf{B} \models \mathcal{H}[h \circ a]$.
-/

theorem Term.eval_hom {X : S → Type} {A B : PartialAlgebra.{u, v, w} Sig}
    (H : PartialAlgebra.Hom A B) (val : ∀ s, X s → Part (A s)) {t : S} (P : Term Sig X t)
    (h : (P.eval A val).Dom) :
    P.eval B (fun s x => (val s x).map (H.map s)) = Part.some (H.map t ((P.eval A val).get h)) := by
  induction P with
  | var x =>
    simp only [Term.eval_var] at h ⊢
    exact Part.eq_some_iff.mpr (Part.mem_map _ (Part.get_mem h))
  | app σ ts ih =>
    obtain ⟨a, ha, hA⟩ := Term.eval_app_dom A val σ h
    have hd : (A.op σ a).Dom := by rw [← hA]; exact h
    have hget : (Term.eval A val (Term.app σ ts)).get h = (A.op σ a).get hd :=
      Part.get_eq_get_of_eq _ _ hA
    have hts : ∀ j, (ts j).eval B (fun s x => (val s x).map (H.map s)) =
        Part.some (H.map _ (a j)) := by
      intro j
      have hj : ((ts j).eval A val).Dom := by rw [ha j]; trivial
      rw [ih j hj]
      congr 2
      exact Part.get_eq_of_mem (by rw [ha j]; exact Part.mem_some _) _
    rw [Term.eval_app_of_eq_some B _ σ hts, hget, H.map_op σ a hd, Part.some_get]

theorem EEq.holdsAll_hom {X : S → Type} {A B : PartialAlgebra.{u, v, w} Sig}
    (H : PartialAlgebra.Hom A B) (val : ∀ s, X s → Part (A s)) {E : Set (EEq Sig X)}
    (h : EEq.HoldsAll A val E) :
    EEq.HoldsAll B (fun s x => (val s x).map (H.map s)) E := by
  intro e he
  obtain ⟨h₁, h₂, heq⟩ := h e he
  refine ⟨?_, ?_, ?_⟩
  · rw [Term.eval_hom H val e.lhs h₁]; trivial
  · rw [Term.eval_hom H val e.rhs h₂]; trivial
  · simp only [Term.eval_hom H val e.lhs h₁, Term.eval_hom H val e.rhs h₂, Part.get_some, heq]

/-!
*Proof of “Values under a homomorphism”.*

By induction on $P$: a homomorphism sends a defined value of $F_\sigma$ to a defined value of
$G_\sigma$, its image. An existence equation whose members have defined and equal values in
$\mathbf{A}$ has, in $\mathbf{B}$, the images of these values as values.
-/

/-!
## Derivors
-/

/-- A *derivor* from a many-sorted signature $(S, \Sigma)$ to another $(T, \Lambda)$ is a pair
$(\varphi, d)$, where $\varphi \colon S \to T$ and $d$ assigns to every
$\sigma \in \Sigma_{\mathbf{s}, s}$ a term
$d(\sigma) \in \mathrm{T}_{\Lambda}(\downarrow\varphi^{\star}(\mathbf{s}))_{\varphi(s)}$.
-/
structure Derivor {T : Type u'} (Sig : Signature.{u, v} S) (Lam : Signature.{u', v'} T) where
  /-- The mapping of sorts `φ`. -/
  sortMap : S → T
  /-- The term `d(σ)` of each operation symbol. -/
  op : ∀ {ws : List S} {s : S}, Sig ws s → Term Lam (Vars (sortMap ∘ ws.get)) (sortMap s)

/-!
### The translation of terms along a derivor

A derivor $(\varphi, d)$ translates the terms of $\Sigma$ with variables in
$\downarrow\kappa$ into terms of $\Lambda$ with variables in $\downarrow(\varphi \circ \kappa)$:
the mapping $d^{\sharp}$ is defined by recursion on terms as

1. (H1) $d^{\sharp}(i) = i$ for a variable $i$;
2. (H2) $d^{\sharp}(\sigma((R_j)_j)) = (d^{\sharp}(R_j))^{\sharp}_j(d(\sigma))$, i.e.,
   $d(\sigma)$ with $d^{\sharp}(R_j)$ substituted for its variable $j$.

The draft defines $d^{\sharp}$ on the terms with variables in $\downarrow\mathbf{s}$; it is the
case of $\kappa$ given by a word.
-/

variable {T : Type u'} {Lam : Signature.{u', v'} T}

/-- The translation `d♯` of terms along a derivor. -/
def Derivor.lift (δ : Derivor Sig Lam) {I : Type} {κ : I → S} :
    {t : S} → Term Sig (Vars κ) t → Term Lam (Vars (δ.sortMap ∘ κ)) (δ.sortMap t)
  | _, .var x => .var ⟨x.1, congrArg δ.sortMap x.2⟩
  | _, .app σ ts => (δ.op σ).subst (famSubst fun j => δ.lift (ts j))

/-!
### Translations commute with substitutions

Let $(\varphi, d)$ be a derivor. Then $d^{\sharp}(\sigma((j)_{j}))= d(\sigma)$ for every
$\sigma \in \Sigma_{\mathbf{s}, s}$, and, for every term $Q \in \mathrm{T}_{\Sigma}(\downarrow\kappa')_t$
and every family $(P_i)_{i}$ with $P_i \in \mathrm{T}_{\Sigma}(\downarrow\kappa)_{\kappa'(i)}$,
$d^{\sharp}((P_i)^{\sharp}_i(Q)) = (d^{\sharp}(P_i))^{\sharp}_i(d^{\sharp}(Q))$.
-/

theorem Derivor.lift_app_vars (δ : Derivor Sig Lam) {ws : List S} {s : S} (σ : Sig ws s) :
    δ.lift (Term.app σ fun j => Term.var (Vars.mk (κ := ws.get) j)) = δ.op σ := by
  simp only [Derivor.lift]
  apply Term.subst_var_of
  rintro _ ⟨j, rfl⟩
  rfl

theorem Derivor.lift_subst (δ : Derivor Sig Lam) {I' : Type} {κ' : I' → S}
    (P : ∀ i, Term Sig (Vars κ) (κ' i)) {t : S} (Q : Term Sig (Vars κ') t) :
    δ.lift (Q.subst (famSubst P)) = (δ.lift Q).subst (famSubst fun i => δ.lift (P i)) := by
  induction Q with
  | var x => obtain ⟨i, rfl⟩ := x; rfl
  | app σ ts ih =>
    simp only [Term.subst, Derivor.lift, ih, Term.subst_subst, famSubst_subst]

/-!
*Proof of “Translations commute with substitutions”.*

The first equation is (H2) together with (H1), the substitution of every variable by itself being
the identity. The second one is proved by induction on $Q$: for a variable it is the definition of
the substitutions, and for $Q = \sigma((Q_j)_j)$ it follows from the induction hypothesis and the
fact that substituting twice is substituting the composite.
-/

/-!
## The category of signatures and derivors
-/

/-!
### Identity and composite derivors

(H3) The *identity* derivor at $(S, \Sigma)$ is $(\mathrm{id}_S, \eta^{\Sigma})$, with
$\eta^{\Sigma}(\sigma) = \sigma((j)_{j \in |\mathbf{s}|})$. The *composite* of $(\varphi, d)$
and a derivor $(\psi, e)$ from $(T, \Lambda)$ to $(U, \Omega)$ is
$(\psi \circ \varphi, e^{\sharp} \circ d)$.
-/

/-- The identity derivor. -/
def Derivor.id (Sig : Signature.{u, v} S) : Derivor Sig Sig where
  sortMap := _root_.id
  op σ := Term.app σ fun j => Term.var (Vars.mk (κ := _root_.id ∘ _) j)

variable {U : Type u''} {Om : Signature.{u'', v''} U}

/-- The composite `(ψ ∘ φ, e♯ ∘ d)` of two derivors. -/
def Derivor.comp (ε : Derivor Lam Om) (δ : Derivor Sig Lam) : Derivor Sig Om where
  sortMap := ε.sortMap ∘ δ.sortMap
  op σ := ε.lift (δ.op σ)

/-!
### Translations along identities and composites

The translation along the identity derivor is the identity, and the translation along a composite
is the composite of the translations: $(e^{\sharp} \circ d)^{\sharp} = e^{\sharp} \circ d^{\sharp}$.
-/

theorem Derivor.lift_id {t : S} (R : Term Sig (Vars κ) t) : (Derivor.id Sig).lift R = R := by
  induction R with
  | var x => rfl
  | app σ ts ih =>
    simp only [Derivor.lift, Derivor.id, Term.subst]
    congr 1; funext j; exact ih j

theorem Derivor.lift_comp (ε : Derivor Lam Om) (δ : Derivor Sig Lam) {t : S}
    (R : Term Sig (Vars κ) t) : (ε.comp δ).lift R = ε.lift (δ.lift R) := by
  induction R with
  | var x => rfl
  | app σ ts ih =>
    show ((ε.comp δ).op σ).subst (famSubst fun j => (ε.comp δ).lift (ts j)) =
      ε.lift ((δ.op σ).subst (famSubst fun j => δ.lift (ts j)))
    rw [ε.lift_subst, funext ih]
    rfl

/-!
*Proof of “Translations along identities and composites”.*

By induction on terms. For the identity, $\eta^{\Sigma}(\sigma)$ with the translated arguments
substituted is $\sigma$ applied to them. For the composite, the case of an operation symbol is
Proposition “Translations commute with substitutions” applied to $e^{\sharp}$.
-/

/-!
### The category Sig_𝔡

The many-sorted signatures and the derivors, with the identities and composites of Construction
“Identity and composite derivors”, form a category $\mathsf{Sig}_{\mathfrak{d}}$.
-/

/-- The many-sorted signatures, as objects of `Sig_𝔡`. -/
structure SigD where
  /-- The set of sorts. -/
  sorts : Type u
  /-- The signature. -/
  sig : Signature.{u, v} sorts

instance SigD.category : CategoryTheory.Category.{max u v} SigD.{u, v} where
  Hom A B := Derivor A.sig B.sig
  id A := Derivor.id A.sig
  comp δ ε := ε.comp δ
  id_comp δ := by
    cases δ with
    | mk φ op =>
      change Derivor.mk (φ ∘ _root_.id) (fun σ => (Derivor.mk φ op).lift _) = _
      congr 1
      funext ws s σ
      exact (Derivor.mk φ op).lift_app_vars σ
  comp_id δ := by
    cases δ with
    | mk φ op =>
      change Derivor.mk (_root_.id ∘ φ) (fun σ => (Derivor.id _).lift (op σ)) = _
      congr 1
      funext ws s σ
      exact Derivor.lift_id _
  assoc δ ε ζ := by
    show Derivor.comp ζ (Derivor.comp ε δ) = Derivor.comp (Derivor.comp ζ ε) δ
    simp only [Derivor.comp]
    congr 1
    funext ws s σ
    exact (Derivor.lift_comp ζ ε _).symm

/-!
*Proof of “The category Sig_𝔡”.*

The composite of $(\varphi, d)$ with the identity is $(\varphi, \eta^{\sharp} \circ d) = (\varphi, d)$
and the composite of the identity with $(\varphi, d)$ is $(\varphi, d^{\sharp} \circ \eta)$,
which is $(\varphi, d)$ by Proposition “Translations commute with substitutions”. Associativity follows from
$(e^{\sharp} \circ d)^{\sharp} = e^{\sharp} \circ d^{\sharp}$, Proposition
“Translations along identities and composites”.
-/

namespace EEq

variable {X : S → Type} {A : PartialAlgebra.{u, v, w} Sig} {val : ∀ s, X s → Part (A s)}

@[simp] lemma holdsAll_empty : HoldsAll A val ∅ := fun _ h => h.elim

lemma holdsAll_mono {H H' : Set (EEq Sig X)} (h : H ⊆ H') : HoldsAll A val H' → HoldsAll A val H :=
  fun h' e he => h' e (h he)

lemma holdsAll_union {H H' : Set (EEq Sig X)} :
    HoldsAll A val (H ∪ H') ↔ HoldsAll A val H ∧ HoldsAll A val H' :=
  ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun ⟨h, h'⟩ e he => he.elim (h e) (h' e)⟩

lemma holdsAll_iUnion {ι : Sort*} {H : ι → Set (EEq Sig X)} :
    HoldsAll A val (⋃ i, H i) ↔ ∀ i, HoldsAll A val (H i) :=
  ⟨fun h i e he => h e (Set.mem_iUnion.mpr ⟨i, he⟩),
    fun h e he => by obtain ⟨i, he⟩ := Set.mem_iUnion.mp he; exact h i e he⟩

lemma holdsAll_biUnion {ι : Type*} {I : Set ι} {H : ι → Set (EEq Sig X)} :
    HoldsAll A val (⋃ i ∈ I, H i) ↔ ∀ i ∈ I, HoldsAll A val (H i) := by
  simp only [holdsAll_iUnion]

lemma holdsAll_insert {e : EEq Sig X} {H : Set (EEq Sig X)} :
    HoldsAll A val (insert e H) ↔ e.Holds A val ∧ HoldsAll A val H :=
  ⟨fun h => ⟨h e (Set.mem_insert _ _), fun e' he' => h e' (Set.mem_insert_of_mem _ he')⟩,
    fun ⟨h, h'⟩ e' he' => (Set.mem_insert_iff.mp he').elim (fun h'' => h'' ▸ h) (h' e')⟩

lemma holdsAll_singleton {e : EEq Sig X} : HoldsAll A val {e} ↔ e.Holds A val :=
  ⟨fun h => h e rfl, fun h _ he => he ▸ h⟩

end EEq

lemma famVal_map {I : Type} {κ : I → S} {A B : S → Type w} (H : ∀ s, A s → B s)
    (a : ∀ i, A (κ i)) :
    (fun s x => (famVal a s x).map (H s)) = famVal fun i => H _ (a i) := by
  funext s x; obtain ⟨i, rfl⟩ := x; rfl

lemma famSubst_eval {I : Type} {κ : I → S} {Y : S → Type} {A : PartialAlgebra.{u, v, w} Sig}
    {val : ∀ s, Y s → Part (A s)} {P : ∀ i, Term Sig Y (κ i)} {c : ∀ i, A (κ i)}
    (h : ∀ i, (P i).eval A val = Part.some (c i)) :
    (fun s x => (famSubst P s x).eval A val) = famVal c := by
  funext s x; obtain ⟨i, rfl⟩ := x; exact h i

/-- The value of a term only depends on the values of its variables. -/
lemma Term.eval_congr_vars {X : S → Type} {A : PartialAlgebra.{u, v, w} Sig}
    {val val' : ∀ s, X s → Part (A s)} :
    ∀ {t : S} (R : Term Sig X t), (∀ p ∈ R.vars, val p.1 p.2 = val' p.1 p.2) →
      R.eval A val = R.eval A val'
  | _, .var x, h => by simpa using h ⟨_, x⟩ rfl
  | _, .app σ ts, h => Term.eval_app_congr σ fun j =>
      eval_congr_vars (ts j) fun p hp => h p (Set.mem_iUnion.mpr ⟨j, hp⟩)

end CategorialAlgebras
