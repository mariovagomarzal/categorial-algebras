import CategorialAlgebras.Dimensions.OmegaDescriptions
import CategorialAlgebras.Dimensions.Adjunctions

/-!
# Retraction of infinite discretization

Truncating an infinite discretization at its initial dimension recovers the
original algebra. The comparisons retain each underlying element.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} (sig : Signature.{u, v} S) (m : ℕ)

/-- Truncation retracts infinite homogeneous discretization on models. -/
noncomputable def homogeneousRoundTripModels :
    homogeneousOmegaDiscretizationModels.{u, v, w} sig m ⋙
      homogeneousOmegaTruncationModels sig m ≅ 𝟭 _ :=
  homogeneousOmegaMixedUpperModels sig (le_refl m) ≪≫ homogeneousDiscretizationModelsSelf sig m

/-- The homogeneous retraction retains each original element. -/
theorem homogeneousRoundTripModels_hom_val
    (B : (Homogeneous.specification (Fin m) sig).Models) (s) (x) :
    (((homogeneousRoundTripModels.{u, v, w} sig m).hom.app B).hom.hom.toMap s x) = x.val.val := by
  have h := inducedIdentityModelsIsoOfEq_hom_heq (homogeneousDiscretization_self sig m) _
    (homogeneousDiscretization_isModel sig (le_refl m)) B s
    (((homogeneousOmegaMixedUpperModels sig (le_refl m)).hom.app B).hom.hom.toMap s x)
  exact (eq_of_heq h).trans (homogeneousOmegaMixedUpperModels_hom_val sig (le_refl m) B s x)

/-- The inverse homogeneous retraction also retains the underlying element. -/
theorem homogeneousRoundTripModels_inv_val
    (B : (Homogeneous.specification (Fin m) sig).Models) (s) (x : B.obj.obj.carrier s) :
    ((((homogeneousRoundTripModels.{u, v, w} sig m).inv.app B).hom.hom.toMap s x).val.val) = x := by
  have h := homogeneousRoundTripModels_hom_val sig m B s
    (((homogeneousRoundTripModels sig m).inv.app B).hom.hom.toMap s x)
  exact h.symm.trans (congrArg (fun f : B ⟶ B => f.hom.hom.toMap s x)
    ((homogeneousRoundTripModels sig m).inv_hom_id_app B))

/-- Truncation retracts infinite heterogeneous discretization on models. -/
noncomputable def heterogeneousRoundTripModels :
    heterogeneousOmegaDiscretizationModels.{u, v, w} sig m ⋙
      heterogeneousOmegaTruncationModels sig m ≅ 𝟭 _ :=
  heterogeneousOmegaMixedUpperModels sig (le_refl m) ≪≫ heterogeneousDiscretizationModelsSelf sig m

/-- The heterogeneous retraction retains the element up to the canonical sort transport. -/
theorem heterogeneousRoundTripModels_hom_val
    (B : (Heterogeneous.specification (Fin (m+1)) sig).Models) (s) (x) :
    HEq (((heterogeneousRoundTripModels.{u, v, w} sig m).hom.app B).hom.hom.toMap s x) x.val.val := by
  have h := inducedIdentityModelsIsoOfEq_hom_heq (heterogeneousDiscretization_self sig m) _
    (heterogeneousDiscretization_isModel sig (le_refl m)) B s
    (((heterogeneousOmegaMixedUpperModels sig (le_refl m)).hom.app B).hom.hom.toMap s x)
  exact h.trans (heterogeneousOmegaMixedUpperModels_hom_heq sig (le_refl m) B s x)

/-- The inverse heterogeneous retraction retains the element up to sort transport. -/
theorem heterogeneousRoundTripModels_inv_val
    (B : (Heterogeneous.specification (Fin (m+1)) sig).Models) (s) (x : B.obj.obj.carrier s) :
    HEq ((((heterogeneousRoundTripModels.{u, v, w} sig m).inv.app B).hom.hom.toMap s x).val.val) x := by
  have h := heterogeneousRoundTripModels_hom_val sig m B s
    (((heterogeneousRoundTripModels sig m).inv.app B).hom.hom.toMap s x)
  exact h.symm.trans (heq_of_eq (congrArg (fun f : B ⟶ B => f.hom.hom.toMap s x)
    ((heterogeneousRoundTripModels sig m).inv_hom_id_app B)))

/-- The homogeneous finite-to-infinite round trip is naturally the identity. -/
noncomputable def homogeneousRoundTripFunctor :
    homogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⋙
      homogeneousOmegaTruncationFunctor sig m ≅ 𝟭 _ :=
  conjugateCompositeIso Homogeneous.modelIsomorphism Homogeneous.omegaModelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousRoundTripModels sig m) ≪≫
      Homogeneous.modelIsomorphism.toEquivalence.unitIso.symm

/-- The heterogeneous finite-to-infinite round trip is naturally the identity. -/
noncomputable def heterogeneousRoundTripFunctor :
    heterogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⋙
      heterogeneousOmegaTruncationFunctor sig m ≅ 𝟭 _ :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousRoundTripModels sig m) ≪≫
      Heterogeneous.modelIsomorphism.toEquivalence.unitIso.symm

end CategorialAlgebras.Omega
