import CategorialAlgebras.Omega.DimensionRetractions

/-!
# Inclusion of homogeneous truncated cells

The counit includes the selected cells. Below the cutoff it preserves restricted
operations; above it the selected cells are identities, so diagonal composition
is preserved by the unit law.
-/

universe u v w

namespace CategorialAlgebras.Omega

open CategoryTheory Presentations Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u} {sig : Signature.{u, v} S} (m : ℕ)

/-- A selected truncation cell is fixed in each dimension above the cutoff. -/
theorem truncated_cell_isCell (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    (k : ℕ) (hk : m ≤ k) (s : S) (x : (omegaTruncatedAlgebra B m).carrier s) :
    (B.sort s).str.IsCell k x.val :=
  (B.sort s).str.isCell_mono hk (omegaTruncatedAlgebra_cell sig m B s x)

/-- The inclusion of selected cells is a categorial algebra homomorphism. -/
noncomputable def homogeneousCounitHom (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) :
    Homogeneous.CategorialAlgebra.Hom (omegaDiscretizedAlgebra (omegaTruncatedAlgebra B m)) B where
  sort s :=
    { toFun := Subtype.val
      map_source k x := by
        change ((if hk : k < m then _ else Homogeneous.CategoryStructure.discrete _).source x).val = _
        by_cases hk : k < m
        · erw [dite_eq_left hk]
          exact truncated_source_val sig (Nat.le_succ m) (omegaRestrictedAlgebra B (m+1)) ⟨k, hk⟩ s x
        · erw [dite_eq_right hk]
          exact (truncated_cell_isCell m B k (Nat.le_of_not_gt hk) s x).symm
      map_target k x := by
        change ((if hk : k < m then _ else Homogeneous.CategoryStructure.discrete _).target x).val = _
        by_cases hk : k < m
        · erw [dite_eq_left hk]
          exact truncated_target_val sig (Nat.le_succ m) (omegaRestrictedAlgebra B (m+1)) ⟨k, hk⟩ s x
        · erw [dite_eq_right hk]
          exact ((B.sort s).str.isCell_iff_target k x.val |>.mp
            (truncated_cell_isCell m B k (Nat.le_of_not_gt hk) s x)).symm
      map_comp k x y z hz := by
        change z ∈ (if hk : k < m then _ else Homogeneous.CategoryStructure.discrete _).comp x y at hz
        by_cases hk : k < m
        · erw [dite_eq_left hk] at hz
          exact (truncated_comp_mem sig (Nat.le_succ m) (omegaRestrictedAlgebra B (m+1)) ⟨k, hk⟩ s x y z).mp hz
        · erw [dite_eq_right hk] at hz
          rcases hz with ⟨rfl, rfl⟩
          have hh := ((B.sort s).str.dim k).comp_source x.val
          rwa [truncated_cell_isCell m B k (Nat.le_of_not_gt hk) s x] at hh }
  map_op _ _ := rfl

/-- The explicit source of the counit realizes the successive induced transformations. -/
noncomputable def homogeneousCounitRealization
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) :
    (omegaDiscretizedAlgebra (omegaTruncatedAlgebra (Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)) m)).toPartialAlgebra ≅
      (homogeneousOmegaDiscretization sig m).transformed ((homogeneousOmegaTruncation sig m).transformed B) :=
  homogeneousOmegaDiscretizationRealization sig m _ ≪≫
    (homogeneousOmegaDiscretization sig m).transformedFunctor.mapIso
      (homogeneousOmegaTruncationRealization sig m _) ≪≫
    ((homogeneousOmegaTruncation sig m).transformedFunctor ⋙
      (homogeneousOmegaDiscretization sig m).transformedFunctor).mapIso
        (eqToIso (Homogeneous.toPartialAlgebra_ofEquations B _))

/-- The counit realization retains the underlying scalar. -/
theorem homogeneousCounitRealization_hom_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) (s : S)
    (x : (omegaTruncatedAlgebra (Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)) m).carrier s) :
    (((homogeneousCounitRealization m B hB).hom.toMap s x).val).val = x.val := by
  change (eqToHom (Homogeneous.toPartialAlgebra_ofEquations B _)).toMap s
    ((homogeneousOmegaTruncationRealization sig m _).hom.toMap s x).val = _
  erw [partial_eqToHom_toMap, cast_eq]
  rfl

/-- The inverse realization removes both cell proofs. -/
theorem homogeneousCounitRealization_inv_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) (s : S)
    (x : (homogeneousOmegaDiscretization sig m).Cell ((homogeneousOmegaTruncation sig m).transformed B) s) :
    ((homogeneousCounitRealization m B hB).inv.toMap s x).val = x.val.val := by
  have hv := homogeneousCounitRealization_hom_val m B hB s
    ((homogeneousCounitRealization m B hB).inv.toMap s x)
  exact hv.symm.trans (congrArg (fun f : _ ⟶ _ => (f.toMap s x).val.val)
    (homogeneousCounitRealization m B hB).inv_hom_id)

/-- The homogeneous counit on partial algebras underlying a model. -/
noncomputable def homogeneousCounitPartial
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) :
    (homogeneousOmegaDiscretization sig m).transformed ((homogeneousOmegaTruncation sig m).transformed B) ⟶ B :=
  (homogeneousCounitRealization m B hB).inv ≫
    (homogeneousCounitHom m (Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩))).toPartialHom ≫
      eqToHom (Homogeneous.toPartialAlgebra_ofEquations B _)

/-- The homogeneous counit is precisely inclusion on underlying elements. -/
@[simp] theorem homogeneousCounitPartial_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) (s : S)
    (x : (homogeneousOmegaDiscretization sig m).Cell ((homogeneousOmegaTruncation sig m).transformed B) s) :
    (homogeneousCounitPartial m B hB).toMap s x = x.val.val := by
  change (eqToHom (Homogeneous.toPartialAlgebra_ofEquations B _)).toMap s _ = _
  erw [partial_eqToHom_toMap, cast_eq]
  exact homogeneousCounitRealization_inv_val m B hB s x

/-- Inclusion of truncated cells is natural on homogeneous models. -/
noncomputable def homogeneousCounit : homogeneousOmegaTruncationModels.{u, v, w} sig m ⋙
    homogeneousOmegaDiscretizationModels sig m ⟶ 𝟭 _ where
  app B := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    (homogeneousCounitPartial m B.obj.obj.obj ⟨B.obj.obj.property, B.obj.property⟩)))
  naturality {B C} f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext s x
    exact (homogeneousCounitPartial_val m C.obj.obj.obj ⟨C.obj.obj.property, C.obj.property⟩ s _).trans
      (congrArg (f.hom.hom.hom.toMap s)
        (homogeneousCounitPartial_val m B.obj.obj.obj ⟨B.obj.obj.property, B.obj.property⟩ s x).symm)

end CategorialAlgebras.Omega
