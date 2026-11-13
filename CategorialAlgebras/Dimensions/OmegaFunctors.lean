import CategorialAlgebras.Dimensions.OmegaModels
import CategorialAlgebras.Dimensions.Functors

/-!
# Truncation and discretization functors in dimension $\omega$

The four functors are induced by generalized hep-derivors. The homogeneous
infinite model category retains the additional finite-dimensional-cell condition.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory

variable {S : Type u} (sig : Signature.{u, v} S) (n : ℕ)

/-- Truncation on all $\omega$-dimensional homogeneous models. -/
noncomputable def homogeneousOmegaTruncationAllModels :
    (Homogeneous.specification ℕ sig).Models ⥤
      (Homogeneous.specification (Fin n) sig).Models :=
  inducedModelFunctor (homogeneousOmegaTruncation sig n) _ _
    (homogeneousOmegaTruncation_isModel sig n)

/-- Truncation restricted to homogeneous models with finite-dimensional cells. -/
noncomputable def homogeneousOmegaTruncationModels :
    Homogeneous.OmegaModels.{u, v, w} sig ⥤
      (Homogeneous.specification (Fin n) sig).Models :=
  Homogeneous.omegaInclusion sig ⋙ homogeneousOmegaTruncationAllModels sig n

/-- Discretization into all $\omega$-dimensional homogeneous models. -/
noncomputable def homogeneousOmegaDiscretizationAllModels :
    (Homogeneous.specification (Fin n) sig).Models ⥤
      (Homogeneous.specification ℕ sig).Models :=
  inducedModelFunctor (homogeneousOmegaDiscretization sig n) _ _
    (homogeneousOmegaDiscretization_isModel sig n)

/-- Discretization corestricts to the models with finite-dimensional cells. -/
noncomputable def homogeneousOmegaDiscretizationModels :
    (Homogeneous.specification (Fin n) sig).Models ⥤ Homogeneous.OmegaModels.{u, v, w} sig :=
  corestrict (homogeneousOmegaDiscretizationAllModels sig n) _ (fun B =>
    homogeneousOmegaDiscretization_finite sig n B.obj.obj ⟨B.obj.property, B.property⟩)

/-- The heterogeneous truncation functor on models. -/
noncomputable def heterogeneousOmegaTruncationModels :
    (Heterogeneous.specification ℕ sig).Models ⥤
      (Heterogeneous.specification (Fin (n + 1)) sig).Models :=
  inducedModelFunctor (heterogeneousOmegaTruncation sig n) _ _
    (heterogeneousOmegaTruncation_isModel sig n)

/-- The heterogeneous discretization functor on models. -/
noncomputable def heterogeneousOmegaDiscretizationModels :
    (Heterogeneous.specification (Fin (n + 1)) sig).Models ⥤
      (Heterogeneous.specification ℕ sig).Models :=
  inducedModelFunctor (heterogeneousOmegaDiscretization sig n) _ _
    (heterogeneousOmegaDiscretization_isModel sig n)

/-- Truncation from homogeneous $\omega$-categorial algebras to dimension $n$. -/
noncomputable def homogeneousOmegaTruncationFunctor :
    Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤ Homogeneous.NCategorialAlgebra n sig :=
  Homogeneous.omegaModelIsomorphism.functor ⋙ homogeneousOmegaTruncationModels sig n ⋙
    Homogeneous.modelIsomorphism.inverse

/-- Discretization from homogeneous dimension $n$ to $\omega$. -/
noncomputable def homogeneousOmegaDiscretizationFunctor :
    Homogeneous.NCategorialAlgebra.{u, v, w} n sig ⥤ Homogeneous.OmegaCategorialAlgebra sig :=
  Homogeneous.modelIsomorphism.functor ⋙ homogeneousOmegaDiscretizationModels sig n ⋙
    Homogeneous.omegaModelIsomorphism.inverse

/-- Truncation from heterogeneous $\omega$-categorial algebras to dimension $n$. -/
noncomputable def heterogeneousOmegaTruncationFunctor :
    Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤ Heterogeneous.NCategorialAlgebra n sig :=
  Heterogeneous.modelIsomorphism.functor ⋙ heterogeneousOmegaTruncationModels sig n ⋙
    Heterogeneous.modelIsomorphism.inverse

/-- Discretization from heterogeneous dimension $n$ to $\omega$. -/
noncomputable def heterogeneousOmegaDiscretizationFunctor :
    Heterogeneous.NCategorialAlgebra.{u, v, w} n sig ⥤ Heterogeneous.OmegaCategorialAlgebra sig :=
  Heterogeneous.modelIsomorphism.functor ⋙ heterogeneousOmegaDiscretizationModels sig n ⋙
    Heterogeneous.modelIsomorphism.inverse

/-- Homogeneous truncation acts by restriction of the original homomorphism. -/
@[simp] theorem homogeneousOmegaTruncationModels_map_val
    {B C : Homogeneous.OmegaModels.{u, v, w} sig} (f : B ⟶ C) (s) (x) :
    (((homogeneousOmegaTruncationModels sig n).map f).hom.hom.toMap s x).val =
      f.hom.hom.hom.toMap s x.val := rfl

/-- Homogeneous discretization retains the original function on cells. -/
@[simp] theorem homogeneousOmegaDiscretizationModels_map_val
    {B C : (Homogeneous.specification (Fin n) sig).Models} (f : B ⟶ C) (s) (x) :
    (((homogeneousOmegaDiscretizationModels.{u, v, w} sig n).map f).hom.hom.hom.toMap s x).val =
      f.hom.hom.toMap s x.val := rfl

/-- Heterogeneous truncation retains each finite-dimensional component. -/
@[simp] theorem heterogeneousOmegaTruncationModels_map_val
    {B C : (Heterogeneous.specification ℕ sig).Models} (f : B ⟶ C) (p) (x) :
    (((heterogeneousOmegaTruncationModels.{u, v, w} sig n).map f).hom.hom.toMap p x).val =
      f.hom.hom.toMap (p.1.val, p.2) x.val := rfl

/-- Heterogeneous discretization repeats the component at the minimum dimension. -/
@[simp] theorem heterogeneousOmegaDiscretizationModels_map_val
    {B C : (Heterogeneous.specification (Fin (n + 1)) sig).Models} (f : B ⟶ C) (p) (x) :
    (((heterogeneousOmegaDiscretizationModels.{u, v, w} sig n).map f).hom.hom.toMap p x).val =
      f.hom.hom.toMap (omegaClamp n p.1, p.2) x.val := rfl

end CategorialAlgebras.Dimensions
