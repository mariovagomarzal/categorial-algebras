import CategorialAlgebras.Preliminaries.PartialAlgebra
import CategorialAlgebras.Preliminaries.Derivor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Basic.Finite.Defs

/-!
# Partial term operations and existence equations

Terms are interpreted at total sorted valuations. An existence equation requires a common
defined value; a quasi-existence equation asserts such an equation under a word-indexed
family of premises. Specifications determine full categories of models, closed under
products. Substitution commutes with evaluation when all assigned terms are defined, and
homomorphisms preserve defined term values and existence equations.
-/

universe u v w x y z i u' v'

namespace CategorialAlgebras

namespace Term

variable {S : Type u} {sig : Signature.{u, v} S} {X : S → Type x}

/-! ## Partial evaluation -/

/-- The partial term operation at a total valuation of the generators. -/
def partialEval {A : PartialAlgebra.{u, v, w} sig} (a : SortedSet.Map X A.carrier) :
    ∀ {s}, Term sig X s → Part (A.carrier s)
  | _, var t => Part.some (a _ t)
  | _, app σ t => (partFamily (fun j => partialEval a (t j))).bind (A.op σ)

/-- Variables are always defined and take their assigned values. -/
@[simp] theorem partialEval_var {A : PartialAlgebra.{u, v, w} sig}
    (a : SortedSet.Map X A.carrier) {s} (t : X s) :
    partialEval a (var t) = Part.some (a s t) := rfl

/-- Evaluation first evaluates every argument and then applies the basic partial operation. -/
@[simp] theorem partialEval_app {A : PartialAlgebra.{u, v, w} sig}
    (a : SortedSet.Map X A.carrier) {b s} (σ : sig b s)
    (t : Word.Family (Term sig X) b) :
    partialEval a (app σ t) =
      (partFamily (fun j => partialEval a (t j))).bind (A.op σ) := rfl

/-- A value of an application is obtained from defined argument values and a basic value. -/
theorem mem_partialEval_app {A : PartialAlgebra.{u, v, w} sig}
    (a : SortedSet.Map X A.carrier) {b s} (σ : sig b s)
    (t : Word.Family (Term sig X) b) (q : A.carrier s) :
    q ∈ partialEval a (app σ t) ↔
      ∃ r : Word.Family A.carrier b, (∀ j, r j ∈ partialEval a (t j)) ∧ q ∈ A.op σ r := by
  simp only [partialEval_app, Part.mem_bind_iff, mem_partFamily]

/-- An application is defined exactly when all arguments and the basic operation are defined. -/
theorem partialEval_app_dom {A : PartialAlgebra.{u, v, w} sig}
    (a : SortedSet.Map X A.carrier) {b s} (σ : sig b s)
    (t : Word.Family (Term sig X) b) :
    (partialEval a (app σ t)).Dom ↔
      ∃ h : ∀ j, (partialEval a (t j)).Dom,
        (A.op σ (fun j => (partialEval a (t j)).get (h j))).Dom :=
  Part.bind_dom

/-- Homomorphisms preserve defined term values at the composed total valuation. -/
theorem partialEval_hom {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, y} sig} (h : PartialAlgebra.Hom A B)
    (a : SortedSet.Map X A.carrier) {s} (t : Term sig X s) {q : A.carrier s}
    (hq : q ∈ partialEval a t) :
    h.toMap s q ∈ partialEval (fun s x => h.toMap s (a s x)) t := by
  induction t with
  | var x =>
    rw [partialEval_var, Part.mem_some_iff] at hq ⊢
    exact congrArg (h.toMap _) hq
  | app σ t ih =>
    obtain ⟨r, hr, hq⟩ := (mem_partialEval_app a σ t q).mp hq
    exact (mem_partialEval_app _ σ t _).mpr
      ⟨fun j => h.toMap _ (r j), fun j => ih j (hr j), h.map_op σ r hq⟩

/-- A homomorphism preserves the domain of every term operation. -/
theorem partialEval_hom_dom {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, y} sig} (h : PartialAlgebra.Hom A B)
    (a : SortedSet.Map X A.carrier) {s} (t : Term sig X s)
    (ht : (partialEval a t).Dom) :
    (partialEval (fun s x => h.toMap s (a s x)) t).Dom :=
  (partialEval_hom h a t (Part.get_mem ht)).1

/-- On defined terms, evaluation commutes with the underlying mapping of a homomorphism. -/
theorem partialEval_hom_get {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, y} sig} (h : PartialAlgebra.Hom A B)
    (a : SortedSet.Map X A.carrier) {s} (t : Term sig X s)
    (ht : (partialEval a t).Dom) :
    (partialEval (fun s x => h.toMap s (a s x)) t).get (partialEval_hom_dom h a t ht) =
      h.toMap s ((partialEval a t).get ht) :=
  Part.get_eq_of_mem (partialEval_hom h a t (Part.get_mem ht)) _

/-- Substitution commutes with evaluation at a valuation realizing every assigned term. -/
theorem partialEval_subst_of_mem {A : PartialAlgebra.{u, v, w} sig} {Y : S → Type y}
    (f : SortedSet.Map Y (Term sig X)) (a : SortedSet.Map X A.carrier)
    (b : SortedSet.Map Y A.carrier) (hf : ∀ s t, b s t ∈ partialEval a (f s t))
    {s} (t : Term sig Y s) : partialEval a (subst f t) = partialEval b t := by
  induction t with
  | var t => exact (Part.eq_some_iff.mpr (hf _ t))
  | app σ t ih =>
    simp only [subst_app, partialEval_app]
    exact congrArg (fun p => (partFamily p).bind (A.op σ)) (funext ih)

/-- The total valuation obtained by evaluating an everywhere defined assignment of terms. -/
def substitutionValuation {A : PartialAlgebra.{u, v, w} sig} {Y : S → Type y}
    (f : SortedSet.Map Y (Term sig X)) (a : SortedSet.Map X A.carrier)
    (hf : ∀ s t, (partialEval a (f s t)).Dom) : SortedSet.Map Y A.carrier :=
  fun s t => (partialEval a (f s t)).get (hf s t)

/-- Equality of partial values gives both the domain and value laws for substitution. -/
theorem partialEval_subst {A : PartialAlgebra.{u, v, w} sig} {Y : S → Type y}
    (f : SortedSet.Map Y (Term sig X)) (a : SortedSet.Map X A.carrier)
    (hf : ∀ s t, (partialEval a (f s t)).Dom) {s} (t : Term sig Y s) :
    partialEval a (subst f t) = partialEval (substitutionValuation f a hf) t :=
  partialEval_subst_of_mem f a _ (fun _ _ => Part.get_mem _) t

/-- The domain law for substitution into a term at an everywhere defined assignment. -/
theorem partialEval_subst_dom {A : PartialAlgebra.{u, v, w} sig} {Y : S → Type y}
    (f : SortedSet.Map Y (Term sig X)) (a : SortedSet.Map X A.carrier)
    (hf : ∀ s t, (partialEval a (f s t)).Dom) {s} (t : Term sig Y s) :
    (partialEval a (subst f t)).Dom ↔
      (partialEval (substitutionValuation f a hf) t).Dom := by
  rw [partialEval_subst f a hf]

/-! ## Evaluation in products -/

/-- Defined term values in a product are exactly the families of component term values. -/
theorem mem_partialEval_product {I : Type i} (A : I → PartialAlgebra.{u, v, w} sig)
    (a : SortedSet.Map X (PartialAlgebra.product A).carrier) {s} (t : Term sig X s)
    (q : (PartialAlgebra.product A).carrier s) :
    q ∈ partialEval a t ↔ ∀ i, q i ∈ partialEval (fun s x => a s x i) t := by
  classical
  constructor
  · intro h i
    exact partialEval_hom (PartialAlgebra.projection A i) a t h
  · intro h
    induction t with
    | var x =>
      simp only [partialEval_var, Part.mem_some_iff] at h ⊢
      exact funext h
    | app σ t ih =>
      have hi i := (mem_partialEval_app _ σ t (q i)).mp (h i)
      choose r hr hq using hi
      apply (mem_partialEval_app a σ t q).mpr
      refine ⟨fun j i => r i j, fun j => ih j _ (fun i => hr i j), ?_⟩
      exact (mem_partFamily _ _).mpr hq

/-- The partial term operation of a product is the assembled family of term operations. -/
theorem partialEval_product {I : Type i} (A : I → PartialAlgebra.{u, v, w} sig)
    (a : SortedSet.Map X (PartialAlgebra.product A).carrier) {s} (t : Term sig X s) :
    partialEval a t = partFamily (fun i => partialEval (fun s x => a s x i) t) := by
  apply Part.ext
  intro q
  exact (mem_partialEval_product A a t q).trans (mem_partFamily _ q).symm

end Term

/-! ## Existence equations -/

/-- Existence equations of type $(X,s)$ are pairs of terms of sort $s$. -/
abbrev EEquation {S : Type u} (sig : Signature.{u, v} S) (X : S → Type x) (s : S) :=
  Term sig X s × Term sig X s

/-- A sorted set of existence equations with the common variable context $X$. -/
abbrev EEquationSet {S : Type u} (sig : Signature.{u, v} S) (X : S → Type x) :=
  SortedSet.Subset (EEquation sig X)

namespace EEquation

variable {S : Type u} {sig : Signature.{u, v} S} {X : S → Type x}

/-- An equation is satisfied when both sides have a common defined value. -/
def Satisfies (A : PartialAlgebra.{u, v, w} sig) (a : SortedSet.Map X A.carrier)
    {s} (e : EEquation sig X s) : Prop :=
  ∃ q, q ∈ Term.partialEval a e.1 ∧ q ∈ Term.partialEval a e.2

/-- Validity quantifies over all total valuations of $X$. -/
def Valid (A : PartialAlgebra.{u, v, w} sig) {s} (e : EEquation sig X s) : Prop :=
  ∀ a : SortedSet.Map X A.carrier, Satisfies A a e

/-- An equation $P \overset{e}{=} P$ holds exactly when $P$ is defined. -/
@[simp] theorem satisfies_self (A : PartialAlgebra.{u, v, w} sig)
    (a : SortedSet.Map X A.carrier) {s} (t : Term sig X s) :
    Satisfies A a (t, t) ↔ (Term.partialEval a t).Dom := by
  constructor
  · rintro ⟨q, h, _⟩
    exact h.1
  · intro h
    exact ⟨_, Part.get_mem h, Part.get_mem h⟩

/-- Satisfaction explicitly requires definedness of both sides and equality of their values. -/
theorem satisfies_iff (A : PartialAlgebra.{u, v, w} sig)
    (a : SortedSet.Map X A.carrier) {s} (e : EEquation sig X s) :
    Satisfies A a e ↔ ∃ hp : (Term.partialEval a e.1).Dom,
      ∃ hq : (Term.partialEval a e.2).Dom,
        (Term.partialEval a e.1).get hp = (Term.partialEval a e.2).get hq := by
  constructor
  · rintro ⟨q, hp, hq⟩
    exact ⟨hp.1, hq.1, hp.2.trans hq.2.symm⟩
  · rintro ⟨hp, hq, h⟩
    exact ⟨_, Part.get_mem hp, h ▸ Part.get_mem hq⟩

/-- Substitute on both sides of an existence equation. -/
def subst {Y : S → Type y} (f : SortedSet.Map X (Term sig Y)) {s}
    (e : EEquation sig X s) : EEquation sig Y s := (Term.subst f e.1, Term.subst f e.2)

/-- Substitution preserves and reflects satisfaction when its assigned terms are defined. -/
theorem satisfies_subst {A : PartialAlgebra.{u, v, w} sig} {Y : S → Type y}
    (f : SortedSet.Map X (Term sig Y)) (a : SortedSet.Map Y A.carrier)
    (hf : ∀ s t, (Term.partialEval a (f s t)).Dom) {s} (e : EEquation sig X s) :
    Satisfies A a (subst f e) ↔ Satisfies A (Term.substitutionValuation f a hf) e := by
  unfold Satisfies subst
  rw [Term.partialEval_subst f a hf, Term.partialEval_subst f a hf]

/-- Homomorphisms preserve existence equations at composed valuations. -/
theorem satisfies_hom {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, y} sig} (h : PartialAlgebra.Hom A B)
    (a : SortedSet.Map X A.carrier) {s} (e : EEquation sig X s)
    (he : Satisfies A a e) : Satisfies B (fun s x => h.toMap s (a s x)) e := by
  obtain ⟨q, hp, hq⟩ := he
  exact ⟨h.toMap _ q, Term.partialEval_hom h a _ hp, Term.partialEval_hom h a _ hq⟩

/-- An existence equation holds in a product exactly when it holds at each projection. -/
theorem satisfies_product_iff {I : Type i} (A : I → PartialAlgebra.{u, v, w} sig)
    (a : SortedSet.Map X (PartialAlgebra.product A).carrier) {s} (e : EEquation sig X s) :
    Satisfies (PartialAlgebra.product A) a e ↔
      ∀ i, Satisfies (A i) (fun s x => a s x i) e := by
  classical
  constructor
  · intro h i
    exact satisfies_hom (PartialAlgebra.projection A i) a e h
  · intro h
    choose q hp hq using h
    exact ⟨q, (Term.mem_partialEval_product A a e.1 q).mpr hp,
      (Term.mem_partialEval_product A a e.2 q).mpr hq⟩

/-- An equation is sortwise finitary when each sort has finitely many variables. -/
def IsSortwiseFinitary {s} (_e : EEquation sig X s) : Prop := ∀ s, Finite (X s)

/-- An equation is finitary when the disjoint union of its variable sorts is finite. -/
def IsFinitary {s} (_e : EEquation sig X s) : Prop := Finite (Σ s, X s)

end EEquation

namespace EEquationSet

variable {S : Type u} {sig : Signature.{u, v} S} {X : S → Type x}

/-- A valuation satisfies a sorted set of equations component by component. -/
def Satisfies (A : PartialAlgebra.{u, v, w} sig) (a : SortedSet.Map X A.carrier)
    (E : EEquationSet sig X) : Prop := ∀ s e, e ∈ E s → EEquation.Satisfies A a e

/-- Every equation of a sorted set holds at every total valuation. -/
def Valid (A : PartialAlgebra.{u, v, w} sig) (E : EEquationSet sig X) : Prop :=
  ∀ a : SortedSet.Map X A.carrier, Satisfies A a E

/-- The componentwise image $f^\sharp[E]$ of a sorted set of equations. -/
def subst {Y : S → Type y} (f : SortedSet.Map X (Term sig Y))
    (E : EEquationSet sig X) : EEquationSet sig Y := fun s => EEquation.subst f '' E s

/-- Substitution of a set of equations obeys the evaluation law at defined assignments. -/
theorem satisfies_subst {A : PartialAlgebra.{u, v, w} sig} {Y : S → Type y}
    (f : SortedSet.Map X (Term sig Y)) (a : SortedSet.Map Y A.carrier)
    (hf : ∀ s t, (Term.partialEval a (f s t)).Dom) (E : EEquationSet sig X) :
    Satisfies A a (subst f E) ↔ Satisfies A (Term.substitutionValuation f a hf) E := by
  constructor
  · intro h s e he
    exact (EEquation.satisfies_subst f a hf e).mp (h s _ ⟨e, he, rfl⟩)
  · rintro h s _ ⟨e, he, rfl⟩
    exact (EEquation.satisfies_subst f a hf e).mpr (h s e he)

/-- Homomorphisms preserve satisfaction of sorted sets of existence equations. -/
theorem satisfies_hom {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, y} sig} (h : PartialAlgebra.Hom A B)
    (a : SortedSet.Map X A.carrier) (E : EEquationSet sig X) (he : Satisfies A a E) :
    Satisfies B (fun s x => h.toMap s (a s x)) E :=
  fun s e hm => EEquation.satisfies_hom h a e (he s e hm)

/-- Derivor image of positional equations, including the union over source sorts mapping
into each target sort. Distinct source sorts may have the same image. -/
def translateWord {T : Type u'} {tau : Signature.{u', v'} T} (c : Derivor sig tau)
    (a : List S) (E : EEquationSet sig (Word.Variables a)) :
    EEquationSet tau (Word.MappedVariables c.sortMap a) := fun t =>
  {e | ∃ s, ∃ h : c.sortMap s = t, ∃ p ∈ E s,
    e = h ▸ (c.translateWord a p.1, c.translateWord a p.2)}

end EEquationSet

/-! ## Quasi-existence equations -/

/-- A quasi-existence equation with one premise for each letter of a word. -/
structure QEEquation {S : Type u} (sig : Signature.{u, v} S) (X : S → Type x)
    (a : List S) (s : S) where
  /-- The word-indexed existence premises. -/
  premises : Word.Family (EEquation sig X) a
  /-- The existence conclusion. -/
  conclusion : EEquation sig X s

/-- The $(S^\star \times S)$-sorted set of quasi-existence equations. -/
abbrev QEEquationSet {S : Type u} (sig : Signature.{u, v} S) (X : S → Type x) :=
  ∀ k : List S × S, Set (QEEquation sig X k.1 k.2)

namespace QEEquation

variable {S : Type u} {sig : Signature.{u, v} S} {X : S → Type x}

/-- Satisfaction of all premises implies satisfaction of the conclusion. -/
def Satisfies (A : PartialAlgebra.{u, v, w} sig) (a : SortedSet.Map X A.carrier)
    {b s} (e : QEEquation sig X b s) : Prop :=
  (∀ j, EEquation.Satisfies A a (e.premises j)) → EEquation.Satisfies A a e.conclusion

/-- A quasi-existence equation holds at every total valuation. -/
def Valid (A : PartialAlgebra.{u, v, w} sig) {b s} (e : QEEquation sig X b s) : Prop :=
  ∀ a : SortedSet.Map X A.carrier, Satisfies A a e

/-- Sortwise finitariness means finitely many variables in each sort. -/
def IsSortwiseFinitary {b s} (_e : QEEquation sig X b s) : Prop := ∀ s, Finite (X s)

/-- Finitariness means finitely many variables in total. -/
def IsFinitary {b s} (_e : QEEquation sig X b s) : Prop := Finite (Σ s, X s)

/-- Quasi-existence validity is preserved by arbitrary products, including empty products. -/
theorem valid_product {I : Type i} (A : I → PartialAlgebra.{u, v, w} sig)
    {b s} (e : QEEquation sig X b s) (h : ∀ i, Valid (A i) e) :
    Valid (PartialAlgebra.product A) e := by
  intro a ha
  apply (EEquation.satisfies_product_iff A a e.conclusion).mpr
  intro i
  apply h i (fun s x => a s x i)
  intro j
  exact (EEquation.satisfies_product_iff A a (e.premises j)).mp (ha j) i

end QEEquation

/-! ## Specifications, models and varieties -/

/-- A quasi-existence specification over a fixed signature, with a total variable context. -/
structure QESpecification {S : Type u} (sig : Signature.{u, v} S) where
  /-- The common sorted variable context. -/
  vars : S → Type x
  /-- The sorted set of quasi-existence axioms. -/
  equations : QEEquationSet sig vars

namespace QESpecification

open CategoryTheory

variable {S : Type u} {sig : Signature.{u, v} S}

/-- An algebra is a model when every specified equation is valid. -/
def IsModel (E : QESpecification.{u, v, x} sig) (A : PartialAlgebra.{u, v, w} sig) : Prop :=
  ∀ k e, e ∈ E.equations k → QEEquation.Valid A e

/-- Models and all partial algebra homomorphisms between them form a full subcategory. -/
abbrev Models (E : QESpecification.{u, v, x} sig) :=
  ObjectProperty.FullSubcategory
    (IsModel.{u, v, w, x} E : ObjectProperty (PartialAlgebra.{u, v, w} sig))

/-- The fully faithful inclusion of models into partial algebras. -/
def inclusion (E : QESpecification.{u, v, x} sig) :
    Models.{u, v, w, x} E ⥤ PartialAlgebra.{u, v, w} sig :=
  ObjectProperty.ι _

/-- The inclusion of models is fully faithful. -/
def inclusionFullyFaithful (E : QESpecification.{u, v, x} sig) :
    (inclusion.{u, v, w, x} E).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- A specification is finitary if each of its equations is finitary. -/
def IsFinitary (E : QESpecification.{u, v, x} sig) : Prop :=
  ∀ k e, e ∈ E.equations k → e.IsFinitary

/-- A specification is sortwise finitary if every axiom has finitely many variables per sort. -/
def IsSortwiseFinitary (E : QESpecification.{u, v, x} sig) : Prop :=
  ∀ k e, e ∈ E.equations k → e.IsSortwiseFinitary

/-- Products of models are models. -/
theorem isModel_product (E : QESpecification.{u, v, x} sig) {I : Type i}
    (A : I → PartialAlgebra.{u, v, w} sig) (h : ∀ i, E.IsModel (A i)) :
    E.IsModel (PartialAlgebra.product A) :=
  fun k e he => QEEquation.valid_product A e (fun i => h i k e he)

end QESpecification

/-- A quasi-existence variety is the class of models of some specification.
The universe of the variable context is fixed by the universe parameter `x`. -/
def IsQEVariety {S : Type u} {sig : Signature.{u, v} S}
    (K : Set (PartialAlgebra.{u, v, w} sig)) : Prop :=
  ∃ E : QESpecification.{u, v, x} sig, ∀ A, A ∈ K ↔ E.IsModel A

/-- A finitary quasi-existence variety admits a specification by finitary equations. -/
def IsFinitaryQEVariety {S : Type u} {sig : Signature.{u, v} S}
    (K : Set (PartialAlgebra.{u, v, w} sig)) : Prop :=
  ∃ E : QESpecification.{u, v, x} sig, E.IsFinitary ∧ ∀ A, A ∈ K ↔ E.IsModel A

/-- Every finitary quasi-existence variety is a quasi-existence variety. -/
theorem IsFinitaryQEVariety.isQEVariety {S : Type u} {sig : Signature.{u, v} S}
    {K : Set (PartialAlgebra.{u, v, w} sig)} (h : IsFinitaryQEVariety.{u, v, w, x} K) :
    IsQEVariety.{u, v, w, x} K := by
  obtain ⟨E, _, he⟩ := h
  exact ⟨E, he⟩

/-- Every quasi-existence variety is closed under products. -/
theorem IsQEVariety.product_mem {S : Type u} {sig : Signature.{u, v} S}
    {K : Set (PartialAlgebra.{u, v, w} sig)} (hK : IsQEVariety.{u, v, w, x} K)
    {I : Type w} (A : I → PartialAlgebra.{u, v, w} sig) (h : ∀ i, A i ∈ K) :
    PartialAlgebra.product A ∈ K := by
  obtain ⟨E, he⟩ := hK
  exact (he _).mpr (E.isModel_product A (fun i => (he _).mp (h i)))

end CategorialAlgebras
