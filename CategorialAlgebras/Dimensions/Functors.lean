import CategorialAlgebras.Dimensions.HomogeneousModels
import CategorialAlgebras.Dimensions.HeterogeneousModels

/-!
# Dimension functors on models and categorial algebras

Each functor is induced by its generalized hep-derivor, restricted to the
source models and corestricted twice. The algebra functors use the strict
model isomorphisms of both presentations.
-/

universe u v w x y

namespace CategorialAlgebras.Dimensions

open CategoryTheory

/-- Restrict an induced partial-algebra functor to source models and corestrict
first to ep-algebras and then to target models. -/
noncomputable def inducedModelFunctor {S T : Type u} {sig : HepSignature.{u, v} S}
    {tau : HepSignature.{u, v} T} (c : GeneralizedHepDerivor sig tau)
    (E : EPSpecification.{u, v, x} sig.toEPSignature)
    (F : EPSpecification.{u, v, y} tau.toEPSignature)
    (hc : ∀ B : PartialAlgebra.{u, v, w} tau.symbol, F.IsModel B →
      E.IsModel (c.transformed B)) : F.Models ⥤ E.Models :=
  let G : F.Models ⥤ PartialAlgebra.{u, v, w} sig.symbol :=
    F.inclusion ⋙ tau.toEPSignature.inclusion ⋙ c.transformedFunctor
  let H : F.Models ⥤ sig.toEPSignature.EPAlg :=
    corestrict G sig.IsEPAlgebra (fun B => by
      exact (hc B.obj.obj ⟨B.obj.property, B.property⟩).1)
  corestrict H _ (fun B => (hc B.obj.obj ⟨B.obj.property, B.property⟩).2)

variable {S : Type u} (sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n)

/-- Heterogeneous discretization preserves models. -/
theorem heterogeneousDiscretization_isModel
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (m + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (m + 1)) sig).IsModel B) :
    (Heterogeneous.specification (Fin (n + 1)) sig).IsModel
      ((heterogeneousDiscretization sig h).transformed B) :=
  heterogeneousDimension_isModel sig (clampDimension m) (clampDimension_saturating m n) B hB

/-- Heterogeneous truncation preserves models. -/
theorem heterogeneousTruncation_isModel
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B) :
    (Heterogeneous.specification (Fin (m + 1)) sig).IsModel
      ((heterogeneousTruncation sig h).transformed B) :=
  heterogeneousDimension_isModel sig (cellInclusion h).toOrderHom
    (orderEmbedding_saturating _) B hB

/-- The induced homogeneous discretization functor on models. -/
noncomputable def homogeneousDiscretizationModels :
    (Homogeneous.specification (Fin m) sig).Models ⥤
      (Homogeneous.specification (Fin n) sig).Models :=
  inducedModelFunctor (homogeneousDiscretization sig h) _ _ (homogeneousDiscretization_isModel sig h)

/-- Homogeneous discretization transported to categorial algebras. -/
noncomputable def homogeneousDiscretizationFunctor :
    Homogeneous.NCategorialAlgebra.{u, v, w} m sig ⥤
      Homogeneous.NCategorialAlgebra.{u, v, w} n sig :=
  Homogeneous.modelIsomorphism.functor ⋙ homogeneousDiscretizationModels sig h ⋙
    Homogeneous.modelIsomorphism.inverse

/-- On model homomorphisms, homogeneous discretization restricts the original map. -/
@[simp] theorem homogeneousDiscretizationModels_map_val
    {B C : (Homogeneous.specification (Fin m) sig).Models}
    (f : B ⟶ C) (s) (x) :
    (((homogeneousDiscretizationModels.{u, v, w} sig h).map f).hom.hom.toMap s x).val =
      f.hom.hom.toMap ((homogeneousDiscretization sig h).sortMap s) x.val := rfl

/-- The induced homogeneous truncation functor on models. -/
noncomputable def homogeneousTruncationModels :
    (Homogeneous.specification (Fin n) sig).Models ⥤
      (Homogeneous.specification (Fin m) sig).Models :=
  inducedModelFunctor (homogeneousTruncation sig h) _ _ (homogeneousTruncation_isModel sig h)

/-- Homogeneous truncation transported to categorial algebras. -/
noncomputable def homogeneousTruncationFunctor :
    Homogeneous.NCategorialAlgebra.{u, v, w} n sig ⥤
      Homogeneous.NCategorialAlgebra.{u, v, w} m sig :=
  Homogeneous.modelIsomorphism.functor ⋙ homogeneousTruncationModels sig h ⋙
    Homogeneous.modelIsomorphism.inverse

/-- On model homomorphisms, homogeneous truncation restricts the original map. -/
@[simp] theorem homogeneousTruncationModels_map_val
    {B C : (Homogeneous.specification (Fin n) sig).Models}
    (f : B ⟶ C) (s) (x) :
    (((homogeneousTruncationModels.{u, v, w} sig h).map f).hom.hom.toMap s x).val =
      f.hom.hom.toMap ((homogeneousTruncation sig h).sortMap s) x.val := rfl

/-- The induced heterogeneous discretization functor on models. -/
noncomputable def heterogeneousDiscretizationModels :
    (Heterogeneous.specification (Fin (m + 1)) sig).Models ⥤
      (Heterogeneous.specification (Fin (n + 1)) sig).Models :=
  inducedModelFunctor (heterogeneousDiscretization sig h) _ _ (heterogeneousDiscretization_isModel sig h)

/-- Heterogeneous discretization transported to categorial algebras. -/
noncomputable def heterogeneousDiscretizationFunctor :
    Heterogeneous.NCategorialAlgebra.{u, v, w} m sig ⥤
      Heterogeneous.NCategorialAlgebra.{u, v, w} n sig :=
  Heterogeneous.modelIsomorphism.functor ⋙ heterogeneousDiscretizationModels sig h ⋙
    Heterogeneous.modelIsomorphism.inverse

/-- On model homomorphisms, heterogeneous discretization restricts the original map. -/
@[simp] theorem heterogeneousDiscretizationModels_map_val
    {B C : (Heterogeneous.specification (Fin (m + 1)) sig).Models}
    (f : B ⟶ C) (s) (x) :
    (((heterogeneousDiscretizationModels.{u, v, w} sig h).map f).hom.hom.toMap s x).val =
      f.hom.hom.toMap ((heterogeneousDiscretization sig h).sortMap s) x.val := rfl

/-- The induced heterogeneous truncation functor on models. -/
noncomputable def heterogeneousTruncationModels :
    (Heterogeneous.specification (Fin (n + 1)) sig).Models ⥤
      (Heterogeneous.specification (Fin (m + 1)) sig).Models :=
  inducedModelFunctor (heterogeneousTruncation sig h) _ _ (heterogeneousTruncation_isModel sig h)

/-- Heterogeneous truncation transported to categorial algebras. -/
noncomputable def heterogeneousTruncationFunctor :
    Heterogeneous.NCategorialAlgebra.{u, v, w} n sig ⥤
      Heterogeneous.NCategorialAlgebra.{u, v, w} m sig :=
  Heterogeneous.modelIsomorphism.functor ⋙ heterogeneousTruncationModels sig h ⋙
    Heterogeneous.modelIsomorphism.inverse

/-- On model homomorphisms, heterogeneous truncation restricts the original map. -/
@[simp] theorem heterogeneousTruncationModels_map_val
    {B C : (Heterogeneous.specification (Fin (n + 1)) sig).Models}
    (f : B ⟶ C) (s) (x) :
    (((heterogeneousTruncationModels.{u, v, w} sig h).map f).hom.hom.toMap s x).val =
      f.hom.hom.toMap ((heterogeneousTruncation sig h).sortMap s) x.val := rfl

end CategorialAlgebras.Dimensions
