import CategorialAlgebras.Dimensions.Comparison
import CategorialAlgebras.Dimensions.HomogeneousCells
import CategorialAlgebras.Dimensions.HeterogeneousComposition

/-!
# Composition of induced dimension functors

The isomorphisms use the canonical comparison of transformations. Empty cell
domains supply its surjectivity for discretization and heterogeneous truncation.
Homogeneous truncation uses reflection of the translated fixed-source equations.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory

variable {S : Type u} (sig : Signature.{u, v} S)

/-- Successive homogeneous discretizations agree naturally with direct discretization. -/
noncomputable def homogeneousDiscretizationModelsComp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    homogeneousDiscretizationModels.{u, v, w} sig hmn ⋙ homogeneousDiscretizationModels sig hnp ≅
      homogeneousDiscretizationModels sig (le_trans hmn hnp) :=
  inducedCompositeModelsNatIsoOfEq _ _ _ _ _ _
    (homogeneousDiscretization_isModel sig hnp) (homogeneousDiscretization_isModel sig hmn)
    (homogeneousDiscretization_isModel sig (le_trans hmn hnp))
    (fun B _ => (homogeneousDiscretization sig hnp).comparison_surjective_of_empty
      (homogeneousDiscretization sig hmn) B (fun _ => rfl))
    (homogeneousDiscretization_comp sig hmn hnp)

/-- Successive homogeneous truncations agree naturally with direct truncation. -/
noncomputable def homogeneousTruncationModelsComp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    homogeneousTruncationModels.{u, v, w} sig hnp ⋙ homogeneousTruncationModels sig hmn ≅
      homogeneousTruncationModels sig (le_trans hmn hnp) :=
  inducedCompositeModelsNatIso _ _ _ (homogeneousTruncation_comp_derivor sig hmn hnp) _ _ _
    (homogeneousTruncation_isModel sig hmn) (homogeneousTruncation_isModel sig hnp)
    (homogeneousTruncation_isModel sig (le_trans hmn hnp))
    (homogeneousTruncation_comparison_surjective hmn hnp)
    (fun B hB s x => by
      change _ ↔ (homogeneousTruncation sig (le_trans hmn hnp)).IsCell B s x
      exact homogeneousTruncation_comp_sameCells hmn hnp B hB s x)

/-- Truncating a homogeneous discretization above the initial dimension agrees naturally
with discretization to the intermediate dimension. -/
noncomputable def homogeneousMixedUpperModels {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    homogeneousDiscretizationModels.{u, v, w} sig (le_trans hmn hnp) ⋙
        homogeneousTruncationModels sig hnp ≅ homogeneousDiscretizationModels sig hmn :=
  inducedCompositeModelsNatIso _ _ _ (homogeneousMixed_upper_derivor sig hmn hnp) _ _ _
    (homogeneousTruncation_isModel sig hnp)
    (homogeneousDiscretization_isModel sig (le_trans hmn hnp))
    (homogeneousDiscretization_isModel sig hmn)
    (homogeneousMixed_comparison_surjective hnp (le_trans hmn hnp))
    (fun B _ s x => by
      change _ ↔ (homogeneousDiscretization sig hmn).IsCell B s x
      exact ⟨fun _ => homogeneousDiscretization_isCell sig hmn B s x,
        fun _ => homogeneousMixed_upper_isCell hmn hnp B s x⟩)

/-- Truncating a homogeneous discretization below the initial dimension agrees naturally
with truncation of the original model. -/
noncomputable def homogeneousMixedLowerModels {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    homogeneousDiscretizationModels.{u, v, w} sig hnp ⋙
        homogeneousTruncationModels sig (le_trans hmn hnp) ≅ homogeneousTruncationModels sig hmn :=
  inducedCompositeModelsNatIso _ _ _ (homogeneousMixed_lower_derivor sig hmn hnp) _ _ _
    (homogeneousTruncation_isModel sig (le_trans hmn hnp))
    (homogeneousDiscretization_isModel sig hnp) (homogeneousTruncation_isModel sig hmn)
    (homogeneousMixed_comparison_surjective (le_trans hmn hnp) hnp)
    (fun B _ s x => by
      change _ ↔ (homogeneousTruncation sig hmn).IsCell B s x
      exact homogeneousMixed_lower_sameCells hmn hnp B s x)

/-- The heterogeneous dimension composite is naturally identified with the direct functor. -/
noncomputable def heterogeneousDiscretizationModelsComp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    heterogeneousDiscretizationModels.{u, v, w} sig hmn ⋙ heterogeneousDiscretizationModels sig hnp ≅
      heterogeneousDiscretizationModels sig (le_trans hmn hnp) :=
  inducedCompositeModelsNatIsoOfEq (heterogeneousDiscretization sig hnp) (heterogeneousDiscretization sig hmn) (heterogeneousDiscretization sig (le_trans hmn hnp)) _ _ _
    (heterogeneousDiscretization_isModel sig hnp) (heterogeneousDiscretization_isModel sig hmn) (heterogeneousDiscretization_isModel sig (le_trans hmn hnp))
    (fun B _ => (heterogeneousDiscretization sig hnp).comparison_surjective_of_empty (heterogeneousDiscretization sig hmn) B (fun _ => rfl))
    (heterogeneousDiscretization_comp sig hmn hnp)

/-- The heterogeneous dimension composite is naturally identified with the direct functor. -/
noncomputable def heterogeneousTruncationModelsComp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    heterogeneousTruncationModels.{u, v, w} sig hnp ⋙ heterogeneousTruncationModels sig hmn ≅
      heterogeneousTruncationModels sig (le_trans hmn hnp) :=
  inducedCompositeModelsNatIsoOfEq (heterogeneousTruncation sig hmn) (heterogeneousTruncation sig hnp) (heterogeneousTruncation sig (le_trans hmn hnp)) _ _ _
    (heterogeneousTruncation_isModel sig hmn) (heterogeneousTruncation_isModel sig hnp) (heterogeneousTruncation_isModel sig (le_trans hmn hnp))
    (fun B _ => (heterogeneousTruncation sig hmn).comparison_surjective_of_empty (heterogeneousTruncation sig hnp) B (fun _ => rfl))
    (heterogeneousTruncation_comp sig hmn hnp)

/-- The heterogeneous dimension composite is naturally identified with the direct functor. -/
noncomputable def heterogeneousMixedUpperModels {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    heterogeneousDiscretizationModels.{u, v, w} sig (le_trans hmn hnp) ⋙ heterogeneousTruncationModels sig hnp ≅
      heterogeneousDiscretizationModels sig hmn :=
  inducedCompositeModelsNatIsoOfEq (heterogeneousTruncation sig hnp) (heterogeneousDiscretization sig (le_trans hmn hnp)) (heterogeneousDiscretization sig hmn) _ _ _
    (heterogeneousTruncation_isModel sig hnp) (heterogeneousDiscretization_isModel sig (le_trans hmn hnp)) (heterogeneousDiscretization_isModel sig hmn)
    (fun B _ => (heterogeneousTruncation sig hnp).comparison_surjective_of_empty (heterogeneousDiscretization sig (le_trans hmn hnp)) B (fun _ => rfl))
    (heterogeneousMixed_upper sig hmn hnp)

/-- The heterogeneous dimension composite is naturally identified with the direct functor. -/
noncomputable def heterogeneousMixedLowerModels {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    heterogeneousDiscretizationModels.{u, v, w} sig hnp ⋙ heterogeneousTruncationModels sig (le_trans hmn hnp) ≅
      heterogeneousTruncationModels sig hmn :=
  inducedCompositeModelsNatIsoOfEq (heterogeneousTruncation sig (le_trans hmn hnp)) (heterogeneousDiscretization sig hnp) (heterogeneousTruncation sig hmn) _ _ _
    (heterogeneousTruncation_isModel sig (le_trans hmn hnp)) (heterogeneousDiscretization_isModel sig hnp) (heterogeneousTruncation_isModel sig hmn)
    (fun B _ => (heterogeneousTruncation sig (le_trans hmn hnp)).comparison_surjective_of_empty (heterogeneousDiscretization sig hnp) B (fun _ => rfl))
    (heterogeneousMixed_lower sig hmn hnp)

end CategorialAlgebras.Dimensions
