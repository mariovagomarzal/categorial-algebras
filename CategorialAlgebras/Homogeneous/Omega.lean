import CategorialAlgebras.Homogeneous.Chain
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite-dimensional cells and the obstruction to quasi-existence axioms

Homogeneous $\omega$-categorial algebras form a full subcategory of the models in
natural-number dimensions. Products of finite chains exhibit a model with a cell of
no finite dimension. Closure of quasi-existence models under products then excludes
any axiomatization of finite-dimensional cells on the fixed homogeneous signature.
-/

universe u v w x

namespace CategorialAlgebras
namespace Homogeneous

open CategoryTheory

variable {S : Type u} {sig : Signature.{u, v} S}

/-- Every cell is fixed by some source operation, expressed in the expanded signature. -/
def FiniteCells (A : PartialAlgebra.{u, max v u, w} (Symbol ℕ sig)) : Prop :=
  ∀ s (x : A.carrier s), ∃ k, x ∈ A.op (.source k s) (single x)

/-- Expansion expresses exactly the usual finite-dimension condition. -/
theorem finiteCells_expansion (A : CategorialAlgebra.{0, u, v, w} ℕ sig) :
    FiniteCells A.toPartialAlgebra ↔ A.FiniteDimensional := by
  constructor
  · intro h s x
    obtain ⟨k, hk⟩ := h s x
    exact ⟨k, (Part.mem_some_iff.mp hk).symm⟩
  · intro h s x
    obtain ⟨k, hk⟩ := h s x
    exact ⟨k, Part.mem_some_iff.mpr hk.symm⟩

/-- A finite word product of finite-dimensional higher categories has finite-dimensional cells. -/
theorem wordProduct_finite (A : SortedCategory.{0, u, w} ℕ S)
    (h : ∀ s, (A s).FiniteDimensional) (a : List S) : (wordProduct A a).FiniteDimensional := by
  classical
  intro x
  choose k hk using fun j : Fin a.length => h _ (x j)
  refine ⟨Finset.univ.sup k, ?_⟩
  change (fun j => ((A (a.get j)).str.dim (Finset.univ.sup k)).source (x j)) = x
  funext j
  exact (A _).str.isCell_mono (Finset.le_sup (Finset.mem_univ j)) (hk j)

/-- The full subcategory of homogeneous ep-models with finite-dimensional cells. -/
abbrev OmegaModels (sig : Signature.{u, v} S) := ObjectProperty.FullSubcategory
  (fun A : (specification ℕ sig).Models => FiniteCells A.obj.obj :
    ObjectProperty (specification ℕ sig).Models)

/-- Inclusion of finite-dimensional models into all homogeneous ep-models. -/
def omegaInclusion (sig : Signature.{u, v} S) : OmegaModels.{u, v, w} sig ⥤
    (specification ℕ sig).Models := ObjectProperty.ι _

/-- The finite-dimensional inclusion is fully faithful. -/
def omegaInclusionFullyFaithful (sig : Signature.{u, v} S) :
    (omegaInclusion.{u, v, w} sig).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- Expansion restricted to homogeneous $\omega$-categorial algebras. -/
def omegaModelFunctor : OmegaCategorialAlgebra.{u, v, w} sig ⥤ OmegaModels sig where
  obj A := ⟨A.obj.toModel, (finiteCells_expansion A.obj).mpr A.property⟩
  map f := ObjectProperty.homMk (modelFunctor.map f.hom)

/-- The restricted expansion is fully faithful. -/
def omegaModelFunctorFullyFaithful : (omegaModelFunctor.{u, v, w} (sig := sig)).FullyFaithful where
  preimage f := ObjectProperty.homMk (modelFunctorFullyFaithful.preimage f.hom)

/-- The restricted expansion is full. -/
instance omegaModelFunctor_full : (omegaModelFunctor.{u, v, w} (sig := sig)).Full :=
  omegaModelFunctorFullyFaithful.full

/-- The restricted expansion is faithful. -/
instance omegaModelFunctor_faithful : (omegaModelFunctor.{u, v, w} (sig := sig)).Faithful :=
  omegaModelFunctorFullyFaithful.faithful

/-- Expansion is also bijective on finite-dimensional objects. -/
theorem omegaModelFunctor_bijective : Function.Bijective
    (omegaModelFunctor.{u, v, w} (sig := sig)).obj := by
  constructor
  · intro A B h
    apply ObjectProperty.FullSubcategory.ext
    exact toModel_bijective.1 (congrArg ObjectProperty.FullSubcategory.obj h)
  · intro A
    let B := ofEquations A.obj.obj.obj (model_equations A.obj)
    have hb : B.FiniteDimensional := by
      apply (finiteCells_expansion B).mp
      rw [show B.toPartialAlgebra = A.obj.obj.obj from toPartialAlgebra_ofEquations _ _]
      exact A.property
    refine ⟨⟨B, hb⟩, ?_⟩
    apply ObjectProperty.FullSubcategory.ext
    exact toModel_ofEquations A.obj

/-- Finite-dimensional expansion is a strict isomorphism of categories. -/
instance omegaModelFunctor_isIso : (omegaModelFunctor.{u, v, w} (sig := sig)).IsIso where
  bijective_obj := omegaModelFunctor_bijective

/-- Homogeneous $\omega$-categorial algebras are the full category of finite-dimensional models. -/
noncomputable def omegaModelIsomorphism :
    IsoCat (OmegaCategorialAlgebra.{u, v, w} sig) (OmegaModels sig) :=
  omegaModelFunctor.asIsomorphism

/-- The class of expanded homogeneous $\omega$-categorial algebras. -/
def IsOmegaAlgebra (A : PartialAlgebra.{u, max v u, w} (Symbol ℕ sig)) : Prop :=
  SatisfiesEquations A ∧ FiniteCells A

/-- A family of finite-chain models, each with a cell above its indexing dimension. -/
def chainFamily (sig : Signature.{u, v} S) (k : ℕ) :
    PartialAlgebra.{u, max v u, w} (Symbol ℕ sig) :=
  (chainAlgebra sig k).toPartialAlgebra

/-- Every factor of the counterexample product is an expanded $\omega$-categorial algebra. -/
theorem chainFamily_isOmega (sig : Signature.{u, v} S) (k : ℕ) :
    IsOmegaAlgebra (chainFamily.{u, v, w} sig k) :=
  ⟨(chainAlgebra.{u, v, w} sig k).satisfiesEquations,
    (finiteCells_expansion _).mpr (chainAlgebra_finite sig k)⟩

/-- The ambient partial-algebra product of the finite-chain family. -/
def chainProduct (sig : Signature.{u, v} S) :
    PartialAlgebra.{u, max v u, w} (Symbol ℕ sig) :=
  PartialAlgebra.product (chainFamily sig)

/-- The chain product still satisfies all homogeneous categorial equations. -/
theorem chainProduct_equations (sig : Signature.{u, v} S) :
    SatisfiesEquations (chainProduct.{u, v, w} sig) :=
  satisfiesEquations_product _ (fun k => (chainFamily_isOmega sig k).1)

/-- The diagonal of top cells has no finite dimension, provided some sort exists. -/
theorem chainProduct_not_finite (sig : Signature.{u, v} S) [Nonempty S] :
    ¬ FiniteCells (chainProduct.{u, v, w} sig) := by
  intro h
  let s := Classical.choice ‹Nonempty S›
  obtain ⟨j, hj⟩ := h s (fun k => chainTop k)
  have hv := (mem_partFamily _ _).mp hj j
  exact boundedChain_not_cell j (Part.mem_some_iff.mp hv).symm

/-- A homogeneous ep-model outside the finite-dimensional full subcategory. -/
def infiniteChainModel (sig : Signature.{u, v} S) :
    (specification ℕ sig).Models.{u, max v u, w, 0} :=
  ⟨⟨chainProduct sig, equations_isEPAlgebra (chainProduct_equations sig)⟩,
    fun _ ⟨e, he⟩ => he ▸ chainProduct_equations sig e⟩

/-- For nonempty sorts, the full subcategory of finite-dimensional models is proper. -/
theorem omegaModels_proper (sig : Signature.{u, v} S) [Nonempty S] :
    ∃ A : (specification ℕ sig).Models.{u, max v u, w, 0}, ¬ FiniteCells A.obj.obj :=
  ⟨infiniteChainModel sig, chainProduct_not_finite sig⟩

/-- No quasi-existence specification on the fixed homogeneous signature defines exactly
its $\omega$-categorial algebras. The common variable context may have any universe. -/
theorem not_qe_axiomatizable (sig : Signature.{u, v} S) [Nonempty S]
    (E : QESpecification.{u, max v u, x} (Symbol ℕ sig)) :
    ¬ (∀ A : PartialAlgebra.{u, max v u, w} (Symbol ℕ sig),
      E.IsModel A ↔ IsOmegaAlgebra A) := by
  intro h
  have hp := E.isModel_product (chainFamily.{u, v, w} sig)
    (fun k => (h _).mpr (chainFamily_isOmega sig k))
  exact chainProduct_not_finite sig ((h _).mp hp).2

/-- No set of contextual quasi-existence equations defines exactly the expanded
$\omega$-categorial algebras on a nonempty set of sorts. -/
theorem not_contextual_axiomatizable (sig : Signature.{u, v} S) [Nonempty S]
    (E : Set (ContextualQEEquation.{u, max v u, x} (Symbol ℕ sig))) :
    ¬ (∀ A : PartialAlgebra.{u, max v u, w} (Symbol ℕ sig),
      (∀ e ∈ E, QEEquation.Valid A e.equation) ↔ IsOmegaAlgebra A) := by
  intro h
  have hp : ∀ e ∈ E, QEEquation.Valid (chainProduct.{u, v, w} sig) e.equation := by
    intro e he
    exact QEEquation.valid_product _ _ (fun k => ((h _).mpr (chainFamily_isOmega sig k)) e he)
  exact chainProduct_not_finite sig ((h _).mp hp).2

/-- Even within the homogeneous ep-signature, no ep-specification can impose exactly
finite-dimensional cells on nonempty sorts. -/
theorem not_ep_axiomatizable (sig : Signature.{u, v} S) [Nonempty S]
    (E : EPSpecification.{u, max v u, x} (epSignature ℕ sig)) :
    ¬ (∀ A : PartialAlgebra.{u, max v u, w} (Symbol ℕ sig),
      E.IsModel A ↔ IsOmegaAlgebra A) := by
  intro h
  have hp : E.IsModel (chainProduct.{u, v, w} sig) := by
    refine ⟨equations_isEPAlgebra (chainProduct_equations sig), ?_⟩
    intro e he
    exact QEEquation.valid_product _ _ (fun k =>
      (((h _).mpr (chainFamily_isOmega sig k)).2 e he))
  exact chainProduct_not_finite sig ((h _).mp hp).2

end Homogeneous
end CategorialAlgebras
