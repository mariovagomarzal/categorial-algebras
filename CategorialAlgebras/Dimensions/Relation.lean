import CategorialAlgebras.Dimensions.Compositions

/-!
# Retraction of discretization by truncation

The induced equal-dimensional functors are naturally identified with identity.
Truncating a discretization recovers the original model; the identification
and its inverse are identities on underlying elements.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory

variable {S : Type u} (sig : Signature.{u, v} S)

/-- Equal-dimensional homogeneous discretization is naturally identity on models. -/
noncomputable def homogeneousDiscretizationModelsSelf (n : ℕ) :
    homogeneousDiscretizationModels.{u, v, w} sig (le_refl n) ≅ 𝟭 _ :=
  inducedIdentityModelsIsoOfEq (homogeneousDiscretization_self sig n) _
    (homogeneousDiscretization_isModel sig (le_refl n))

/-- Equal-dimensional homogeneous truncation is naturally identity on models. -/
noncomputable def homogeneousTruncationModelsSelf (n : ℕ) :
    homogeneousTruncationModels.{u, v, w} sig (le_refl n) ≅ 𝟭 _ :=
  inducedIdentityModelsIsoOfEq (homogeneousTruncation_self sig n) _
    (homogeneousTruncation_isModel sig (le_refl n))

/-- Truncation retracts homogeneous discretization naturally on models. -/
noncomputable def homogeneousRoundTripModels {m n : ℕ} (h : m ≤ n) :
    homogeneousDiscretizationModels.{u, v, w} sig h ⋙ homogeneousTruncationModels sig h ≅ 𝟭 _ :=
  homogeneousMixedUpperModels sig (le_refl m) h ≪≫ homogeneousDiscretizationModelsSelf sig m

/-- The homogeneous round-trip identification retains the original underlying element. -/
theorem homogeneousRoundTripModels_hom_val {m n : ℕ} (h : m ≤ n)
    (B : (Homogeneous.specification (Fin m) sig).Models) (s)
    (x : ((homogeneousDiscretizationModels sig h ⋙ homogeneousTruncationModels sig h).obj B).obj.obj.carrier s) :
    HEq (((homogeneousRoundTripModels.{u, v, w} sig h).hom.app B).hom.hom.toMap s x) x.val.val := by
  apply HEq.trans (inducedIdentityModelsIsoOfEq_hom_heq
    (homogeneousDiscretization_self sig m) _
    (homogeneousDiscretization_isModel sig (le_refl m)) B s _)
  exact inducedCompositeModelsNatIso_hom_heq
    (homogeneousTruncation sig h) (homogeneousDiscretization sig h)
    (homogeneousDiscretization sig (le_refl m)) (homogeneousMixed_upper_derivor sig (le_refl m) h)
    (Homogeneous.specification (Fin m) sig) (Homogeneous.specification (Fin n) sig)
    (Homogeneous.specification (Fin m) sig)
    (homogeneousTruncation_isModel sig h) (homogeneousDiscretization_isModel sig h)
    (homogeneousDiscretization_isModel sig (le_refl m))
    (homogeneousMixed_comparison_surjective h h)
    (fun B _ s x => by
      change _ ↔ (homogeneousDiscretization sig (le_refl m)).IsCell B s x
      exact ⟨fun _ => homogeneousDiscretization_isCell sig (le_refl m) B s x,
        fun _ => homogeneousMixed_upper_isCell (le_refl m) h B s x⟩) B s x

/-- The inverse homogeneous round-trip identification also retains the original element. -/
theorem homogeneousRoundTripModels_inv_val {m n : ℕ} (h : m ≤ n)
    (B : (Homogeneous.specification (Fin m) sig).Models) (s) (x : B.obj.obj.carrier s) :
    HEq ((((homogeneousRoundTripModels.{u, v, w} sig h).inv.app B).hom.hom.toMap s x).val.val) x := by
  have hv := homogeneousRoundTripModels_hom_val sig h B s
    (((homogeneousRoundTripModels sig h).inv.app B).hom.hom.toMap s x)
  exact hv.symm.trans (heq_of_eq (congrArg
    (fun f : B ⟶ B => f.hom.hom.toMap s x) ((homogeneousRoundTripModels sig h).inv_hom_id_app B)))

/-- Equal-dimensional heterogeneous discretization is naturally identity on models. -/
noncomputable def heterogeneousDiscretizationModelsSelf (n : ℕ) :
    heterogeneousDiscretizationModels.{u, v, w} sig (le_refl n) ≅ 𝟭 _ :=
  inducedIdentityModelsIsoOfEq (heterogeneousDiscretization_self sig n) _
    (heterogeneousDiscretization_isModel sig (le_refl n))

/-- Equal-dimensional heterogeneous truncation is naturally identity on models. -/
noncomputable def heterogeneousTruncationModelsSelf (n : ℕ) :
    heterogeneousTruncationModels.{u, v, w} sig (le_refl n) ≅ 𝟭 _ :=
  inducedIdentityModelsIsoOfEq (heterogeneousTruncation_self sig n) _
    (heterogeneousTruncation_isModel sig (le_refl n))

/-- Truncation retracts heterogeneous discretization naturally on models. -/
noncomputable def heterogeneousRoundTripModels {m n : ℕ} (h : m ≤ n) :
    heterogeneousDiscretizationModels.{u, v, w} sig h ⋙ heterogeneousTruncationModels sig h ≅ 𝟭 _ :=
  heterogeneousMixedUpperModels sig (le_refl m) h ≪≫ heterogeneousDiscretizationModelsSelf sig m

/-- The heterogeneous round-trip identification retains the original underlying element. -/
theorem heterogeneousRoundTripModels_hom_val {m n : ℕ} (h : m ≤ n)
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) (s)
    (x : ((heterogeneousDiscretizationModels sig h ⋙ heterogeneousTruncationModels sig h).obj B).obj.obj.carrier s) :
    HEq (((heterogeneousRoundTripModels.{u, v, w} sig h).hom.app B).hom.hom.toMap s x) x.val.val := by
  apply HEq.trans (inducedIdentityModelsIsoOfEq_hom_heq
    (heterogeneousDiscretization_self sig m) _
    (heterogeneousDiscretization_isModel sig (le_refl m)) B s _)
  exact inducedCompositeModelsNatIso_hom_heq
    (heterogeneousTruncation sig h) (heterogeneousDiscretization sig h)
    (heterogeneousDiscretization sig (le_refl m))
    (congrArg GeneralizedHepDerivor.toDerivor (heterogeneousMixed_upper sig (le_refl m) h))
    (Heterogeneous.specification (Fin (m + 1)) sig) (Heterogeneous.specification (Fin (n + 1)) sig)
    (Heterogeneous.specification (Fin (m + 1)) sig)
    (heterogeneousTruncation_isModel sig h) (heterogeneousDiscretization_isModel sig h)
    (heterogeneousDiscretization_isModel sig (le_refl m))
    (fun B _ => (heterogeneousTruncation sig h).comparison_surjective_of_empty
      (heterogeneousDiscretization sig h) B (fun _ => rfl))
    (fun B _ s x => cells_of_eq (heterogeneousMixed_upper sig (le_refl m) h) B s x) B s x

/-- The inverse heterogeneous round-trip identification also retains the original element. -/
theorem heterogeneousRoundTripModels_inv_val {m n : ℕ} (h : m ≤ n)
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) (s) (x : B.obj.obj.carrier s) :
    HEq ((((heterogeneousRoundTripModels.{u, v, w} sig h).inv.app B).hom.hom.toMap s x).val.val) x := by
  have hv := heterogeneousRoundTripModels_hom_val sig h B s
    (((heterogeneousRoundTripModels sig h).inv.app B).hom.hom.toMap s x)
  exact hv.symm.trans (heq_of_eq (congrArg
    (fun f : B ⟶ B => f.hom.hom.toMap s x) ((heterogeneousRoundTripModels sig h).inv_hom_id_app B)))

end CategorialAlgebras.Dimensions
