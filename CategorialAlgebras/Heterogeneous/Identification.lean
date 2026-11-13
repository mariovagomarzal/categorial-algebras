import CategorialAlgebras.Heterogeneous.Models
import Mathlib.CategoryTheory.IsoCat

/-!
# The identification with models

Expansion is fully faithful and bijective on objects, with inverse given by recovery.
It acts as the identity on the sorted carriers and on the functions of homomorphisms.
-/

universe i u v w

namespace CategorialAlgebras
namespace Heterogeneous

open CategoryTheory

variable {I : Type i} [Preorder I] {S : Type u} {sig : Signature.{u, v} S}

/-! ## Inverse constructions on objects -/

/-- Recovery after expansion returns the original categorial algebra. -/
@[simp] theorem ofEquations_toPartialAlgebra (A : CategorialAlgebra.{i, u, v, w} I sig) :
    ofEquations A.toPartialAlgebra A.satisfiesEquations = A := by
  cases A with
  | mk sort op =>
    change CategorialAlgebra.mk sort _ = CategorialAlgebra.mk sort op
    apply congrArg (CategorialAlgebra.mk sort)
    funext a s σ
    apply Functor.ext
    funext k x
    exact congrArg ((op σ).toFun k)
      ((dimensionFamily (A := fun ks => (sort ks.2).carrier ks.1) k a).apply_symm_apply x)

/-- Expand a categorial algebra as an object of the ep-model category. -/
def CategorialAlgebra.toModel (A : CategorialAlgebra.{i, u, v, w} I sig) :
    (specification I sig).Models :=
  ⟨⟨A.toPartialAlgebra, equations_isEPAlgebra A.satisfiesEquations⟩,
    fun _ ⟨e, he⟩ => he ▸ A.satisfiesEquations e⟩

/-- The contextual equations hold in every bundled ep-model. -/
theorem model_equations (A : (specification I sig).Models) : SatisfiesEquations A.obj.obj :=
  fun e => A.property _ ⟨e, rfl⟩

/-- Recovery gives the unique preimage of each ep-model. -/
theorem toModel_ofEquations (A : (specification I sig).Models) :
    (ofEquations A.obj.obj (model_equations A)).toModel = A := by
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  exact toPartialAlgebra_ofEquations _ _

/-- Expansion is bijective on objects, including empty sorted carriers. -/
theorem toModel_bijective : Function.Bijective
    (CategorialAlgebra.toModel : CategorialAlgebra.{i, u, v, w} I sig →
      (specification I sig).Models) := by
  constructor
  · intro A B h
    have he := congrArg (fun M => ofEquations M.obj.obj (model_equations M)) h
    change ofEquations A.toPartialAlgebra _ = ofEquations B.toPartialAlgebra _ at he
    simpa only [ofEquations_toPartialAlgebra] using he
  · intro A
    exact ⟨_, toModel_ofEquations A⟩

/-! ## Isomorphism of categories -/

/-- The expansion functor to the category of ep-models. -/
def modelFunctor : CategorialAlgebra.{i, u, v, w} I sig ⥤
    (specification I sig).Models where
  obj := CategorialAlgebra.toModel
  map f := ObjectProperty.homMk (ObjectProperty.homMk f.toPartialHom)

/-- Expansion is fully faithful, since its morphisms have exactly the same functions. -/
def modelFunctorFullyFaithful : (modelFunctor (I := I) (sig := sig)).FullyFaithful where
  preimage f := CategorialAlgebra.Hom.ofPartialHom f.hom.hom

/-- The expansion functor is full. -/
instance modelFunctor_full : (modelFunctor (I := I) (sig := sig)).Full :=
  modelFunctorFullyFaithful.full

/-- The expansion functor is faithful. -/
instance modelFunctor_faithful : (modelFunctor (I := I) (sig := sig)).Faithful :=
  modelFunctorFullyFaithful.faithful

/-- Every ep-model is the expansion of a categorial algebra on its own carriers. -/
instance modelFunctor_essSurj : (modelFunctor (I := I) (sig := sig)).EssSurj where
  mem_essImage A := ⟨ofEquations A.obj.obj (model_equations A), ⟨eqToIso (toModel_ofEquations A)⟩⟩

/-- Expansion is a strict isomorphism of categories: it is full, faithful and object-bijective. -/
instance modelFunctor_isIso : (modelFunctor (I := I) (sig := sig)).IsIso where
  bijective_obj := toModel_bijective

/-- Categorial algebras and ep-models are isomorphic categories. -/
noncomputable def modelIsomorphism : IsoCat (CategorialAlgebra.{i, u, v, w} I sig)
    (specification I sig).Models := modelFunctor.asIsomorphism

/-- Expansion is an equivalence of categories. -/
instance modelFunctor_isEquivalence : (modelFunctor (I := I) (sig := sig)).IsEquivalence where

/-- Categorial algebras are equivalent to ep-models; expansion is also bijective on objects. -/
noncomputable def modelEquivalence : CategorialAlgebra.{i, u, v, w} I sig ≌
    (specification I sig).Models := modelFunctor.asEquivalence

/-- The presentation leaves every sorted carrier unchanged. -/
@[simp] theorem modelFunctor_carrier (A : CategorialAlgebra.{i, u, v, w} I sig) :
    (modelFunctor.obj A).obj.obj.carrier = A.carrier := rfl

/-! ## Finite dimensions and dimension $\omega$ -/

/-- The finite-dimensional identification includes dimensions $0,\ldots,n$. -/
noncomputable abbrev nModelIsomorphism (n : ℕ) {S : Type u} (sig : Signature.{u, v} S) :
    IsoCat (NCategorialAlgebra.{u, v, w} n sig)
      (specification (Fin (n + 1)) sig).Models := modelIsomorphism

/-- In dimension $\omega$ all models are categorial algebras without an extra condition. -/
noncomputable abbrev omegaModelIsomorphism {S : Type u} (sig : Signature.{u, v} S) :
    IsoCat (OmegaCategorialAlgebra.{u, v, w} sig) (specification ℕ sig).Models := modelIsomorphism

end Heterogeneous
end CategorialAlgebras
