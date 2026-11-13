import CategorialAlgebras.Dimensions.Relation

/-!
# Inclusion of homogeneous truncated cells

The counit includes the selected cells. Below the cutoff it preserves restricted
operations; above it the selected cells are identities, so diagonal composition
is preserved by the unit law.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S : Type u} {sig : Signature.{u, v} S} {m n : ℕ} (h : m ≤ n)

/-- A selected truncation cell is fixed in each dimension above the cutoff. -/
theorem truncated_cell_isCell (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin n) (hk : m ≤ k.val) (s : S) (x : (truncatedAlgebra h B).carrier s) :
    (B.sort s).str.IsCell k x.val :=
  (isFiniteCell_castSucc _ k _).mp (isFiniteCell_mono _
    (show cellInclusion h (Fin.last m) ≤ k.castSucc from hk) (x.is_finite_cell B))

/-- The inclusion of selected cells is a categorial algebra homomorphism. -/
noncomputable def homogeneousCounitHom (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    Homogeneous.CategorialAlgebra.Hom (discretizedAlgebra (truncatedAlgebra h B) n) B where
  sort s :=
    { toFun := Subtype.val
      map_source k x := by
        change ((if hk : k.val < m then _ else Homogeneous.CategoryStructure.discrete _).source x).val = _
        by_cases hk : k.val < m
        · erw [dite_eq_left hk]
          exact truncated_source_val sig h B ⟨k.val, hk⟩ s x
        · erw [dite_eq_right hk]
          exact (truncated_cell_isCell h B k (Nat.le_of_not_gt hk) s x).symm
      map_target k x := by
        change ((if hk : k.val < m then _ else Homogeneous.CategoryStructure.discrete _).target x).val = _
        by_cases hk : k.val < m
        · erw [dite_eq_left hk]
          exact truncated_target_val sig h B ⟨k.val, hk⟩ s x
        · erw [dite_eq_right hk]
          exact ((B.sort s).str.isCell_iff_target k x.val |>.mp
            (truncated_cell_isCell h B k (Nat.le_of_not_gt hk) s x)).symm
      map_comp k x y z hz := by
        change z ∈ (if hk : k.val < m then _ else Homogeneous.CategoryStructure.discrete _).comp x y at hz
        by_cases hk : k.val < m
        · erw [dite_eq_left hk] at hz
          exact (truncated_comp_mem sig h B ⟨k.val, hk⟩ s x y z).mp hz
        · erw [dite_eq_right hk] at hz
          rcases hz with ⟨rfl, rfl⟩
          have hh := ((B.sort s).str.dim k).comp_source x.val
          rwa [truncated_cell_isCell h B k (Nat.le_of_not_gt hk) s x] at hh }
  map_op _ _ := rfl

/-- The explicit source of the counit realizes the successive induced transformations. -/
noncomputable def homogeneousCounitRealization
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    (discretizedAlgebra (truncatedAlgebra h (recoveredAlgebra B hB)) n).toPartialAlgebra ≅
      (homogeneousDiscretization sig h).transformed ((homogeneousTruncation sig h).transformed B) :=
  homogeneousDiscretizationRealization sig h (truncatedAlgebra h (recoveredAlgebra B hB)) ≪≫
    (homogeneousDiscretizationPartialFunctor sig h).mapIso
      (eqToIso (homogeneousTruncation_transformed sig h (recoveredAlgebra B hB)).symm) ≪≫
    (homogeneousTruncationPartialFunctor sig h ⋙ homogeneousDiscretizationPartialFunctor sig h).mapIso
      (eqToIso (Homogeneous.toPartialAlgebra_ofEquations B _))

/-- The counit realization retains the underlying scalar. -/
theorem homogeneousCounitRealization_hom_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) (s : S)
    (x : (truncatedAlgebra h (recoveredAlgebra B hB)).carrier s) :
    (((homogeneousCounitRealization h B hB).hom.toMap s x).val).val = x.val := by
  change (eqToHom (Homogeneous.toPartialAlgebra_ofEquations B _)).toMap s
    (((eqToHom (homogeneousTruncation_transformed sig h (recoveredAlgebra B hB)).symm).toMap s x).val) = _
  erw [partial_eqToHom_toMap, partial_eqToHom_toMap]
  erw [cast_eq, cast_eq]

/-- The inverse realization removes both cell proofs. -/
theorem homogeneousCounitRealization_inv_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) (s : S)
    (x : (homogeneousDiscretization sig h).Cell ((homogeneousTruncation sig h).transformed B) s) :
    ((homogeneousCounitRealization h B hB).inv.toMap s x).val = x.val.val := by
  have hv := homogeneousCounitRealization_hom_val h B hB s
    ((homogeneousCounitRealization h B hB).inv.toMap s x)
  exact hv.symm.trans (congrArg (fun f : _ ⟶ _ => (f.toMap s x).val.val)
    (homogeneousCounitRealization h B hB).inv_hom_id)

/-- The homogeneous counit on partial algebras underlying a model. -/
noncomputable def homogeneousCounitPartial
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    (homogeneousDiscretization sig h).transformed ((homogeneousTruncation sig h).transformed B) ⟶ B :=
  (homogeneousCounitRealization h B hB).inv ≫
    (homogeneousCounitHom h (recoveredAlgebra B hB)).toPartialHom ≫
      eqToHom (Homogeneous.toPartialAlgebra_ofEquations B _)

/-- The homogeneous counit is precisely inclusion on underlying elements. -/
@[simp] theorem homogeneousCounitPartial_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) (s : S)
    (x : (homogeneousDiscretization sig h).Cell ((homogeneousTruncation sig h).transformed B) s) :
    (homogeneousCounitPartial h B hB).toMap s x = x.val.val := by
  change (eqToHom (Homogeneous.toPartialAlgebra_ofEquations B _)).toMap s _ = _
  erw [partial_eqToHom_toMap, cast_eq]
  exact homogeneousCounitRealization_inv_val h B hB s x

/-- Inclusion of truncated cells is natural on homogeneous models. -/
noncomputable def homogeneousCounit : homogeneousTruncationModels.{u, v, w} sig h ⋙
    homogeneousDiscretizationModels sig h ⟶ 𝟭 _ where
  app B := ObjectProperty.homMk (ObjectProperty.homMk
    (homogeneousCounitPartial h B.obj.obj ⟨B.obj.property, B.property⟩))
  naturality {B C} f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext s x
    exact (homogeneousCounitPartial_val h C.obj.obj ⟨C.obj.property, C.property⟩ s _).trans
      (congrArg (f.hom.hom.toMap s)
        (homogeneousCounitPartial_val h B.obj.obj ⟨B.obj.property, B.property⟩ s x).symm)

end CategorialAlgebras.Dimensions
