import CategorialAlgebras.Omega.Graduation
import CategorialAlgebras.Omega.Isomorphisms
import CategorialAlgebras.Omega.DimensionRetractions
import CategorialAlgebras.Presentations.GraduationModels

/-!
# Finite restrictions of explicit graduation

Graduating the algebra of cutoff cells and restricting $\omega$-dimensional
graduation have the same elements. The comparison flattens the two subtypes.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (n : ℕ)

/-- Package a fixed-source element as a cell of the explicit finite truncation. -/
def cutoffCell (s : S) (x : A.carrier s) (hx : (A.sort s).str.IsCell n x) :
    (omegaTruncatedAlgebra A n).carrier s :=
  ⟨x, (homogeneousTruncation_isCell_iff sig (Nat.le_succ n)
    (omegaRestrictedAlgebra A (n+1)) s x).mpr (fun _ => hx)⟩

/-- Sources in explicit truncation restrict the original sources. -/
theorem cutoff_source_val (k : Fin n) (s : S) (x : (omegaTruncatedAlgebra A n).carrier s) :
    ((((omegaTruncatedAlgebra A n).sort s).str.dim k).source x).val =
      ((A.sort s).str.dim k.val).source x.val :=
  truncated_source_val sig (Nat.le_succ n) (omegaRestrictedAlgebra A (n+1)) k s x

/-- Targets in explicit truncation restrict the original targets. -/
theorem cutoff_target_val (k : Fin n) (s : S) (x : (omegaTruncatedAlgebra A n).carrier s) :
    ((((omegaTruncatedAlgebra A n).sort s).str.dim k).target x).val =
      ((A.sort s).str.dim k.val).target x.val :=
  truncated_target_val sig (Nat.le_succ n) (omegaRestrictedAlgebra A (n+1)) k s x

/-- Restrict explicit $\omega$-dimensional graduation to the first $n+1$ carriers. -/
noncomputable def finiteGraduatedAlgebra : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig where
  sort s := ⟨fun k => GraduatedCell A k.val s,
    (graduatedSort A s).str.restrict (omegaInclusion (n+1))⟩
  op σ :=
    { toFun k := (graduatedAlgebra A).op σ |>.toFun k.val
      map_source j k h x := ((graduatedAlgebra A).op σ).map_source j.val k.val h x
      map_target j k h x := ((graduatedAlgebra A).op σ).map_target j.val k.val h x
      map_identity j k h x := ((graduatedAlgebra A).op σ).map_identity j.val k.val h x
      map_comp j k h x y z hz := ((graduatedAlgebra A).op σ).map_comp j.val k.val h x y z hz }

/-- Flatten a cell of finite graduation into the original fixed-source subtype. -/
def finiteGraduationCell (k : Fin (n+1)) (s : S)
    (x : Presentations.GraduatedCell (omegaTruncatedAlgebra A n) k s) : GraduatedCell A k.val s := by
  refine ⟨x.val.val, ?_⟩
  by_cases hk : k.val < n
  · have hx := x.is_finite_cell _ hk
    exact (cutoff_source_val A n ⟨k.val, hk⟩ s x.val).symm.trans (congrArg Subtype.val hx)
  · have he : k.val = n := le_antisymm (Nat.le_of_lt_succ k.isLt) (Nat.le_of_not_gt hk)
    rw [he]
    exact omegaTruncatedAlgebra_cell sig n A s x.val

/-- Flattening finite graduated cells is a bijection. -/
theorem finiteGraduationCell_bijective (k : Fin (n+1)) (s : S) :
    Function.Bijective (finiteGraduationCell A n k s) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : GraduatedCell A k.val s => z.val) h
  · intro y
    let x := cutoffCell A n s y.val ((A.sort s).str.isCell_mono (Nat.le_of_lt_succ k.isLt) y.property)
    refine ⟨Presentations.graduatedCell _ x (fun hk => ?_), Subtype.ext rfl⟩
    apply Subtype.ext
    exact (cutoff_source_val A n ⟨k.val, hk⟩ s x).trans y.property

/-- The flattening map preserves every heterogeneous operation. -/
noncomputable def finiteGraduationHom :
    Presentations.graduatedAlgebra (omegaTruncatedAlgebra A n) ⟶ finiteGraduatedAlgebra A n where
  sort s :=
    { toFun k := finiteGraduationCell A n k s
      map_source j k h x := Subtype.ext (cutoff_source_val A n (Presentations.lowerDimension h) s x.val)
      map_target j k h x := Subtype.ext (cutoff_target_val A n (Presentations.lowerDimension h) s x.val)
      map_identity _ _ _ _ := Subtype.ext rfl
      map_comp j k h x y z hz := by
        apply (mem_graduatedComp A h _ _ _).mpr
        exact (truncated_comp_mem sig (Nat.le_succ n) (omegaRestrictedAlgebra A (n+1))
          (Presentations.lowerDimension h) s x.val y.val z.val).mp
            ((Presentations.mem_graduatedComp _ h x y z).mp hz) }
  map_op _ _ _ := Subtype.ext rfl

/-- Finite graduation and restriction agree by the isomorphism flattening their cell subtypes. -/
noncomputable def finiteGraduationIso :
    Presentations.graduatedAlgebra (omegaTruncatedAlgebra A n) ≅ finiteGraduatedAlgebra A n :=
  heterogeneousIsoOfBijective (finiteGraduationHom A n) (fun s k => finiteGraduationCell_bijective A n k s)

/-- The finite comparison retains the underlying element. -/
@[simp] theorem finiteGraduationIso_hom_val (k : Fin (n+1)) (s : S)
    (x : Presentations.GraduatedCell (omegaTruncatedAlgebra A n) k s) :
    ((((finiteGraduationIso A n).hom.sort s).toFun k x).val) = x.val.val := rfl

/-- The inverse finite comparison also retains the underlying element. -/
theorem finiteGraduationIso_inv_val (k : Fin (n+1)) (s : S)
    (x : GraduatedCell A k.val s) :
    (((finiteGraduationIso A n).inv.sort s).toFun k x).val.val = x.val :=
  congrArg (fun f : finiteGraduatedAlgebra A n ⟶ finiteGraduatedAlgebra A n =>
    ((f.sort s).toFun k x).val) (finiteGraduationIso A n).inv_hom_id

/-- The explicit finite graduation is the strict reindexing, up to identity on carriers. -/
noncomputable def finiteGraduationReindexIso :
    finiteGraduatedAlgebra A n ≅ reindexedAlgebra (graduatedAlgebra A)
      (omegaInclusion (n+1)).toOrderHom (orderEmbedding_saturating _) :=
  heterogeneousIsoOfBijective
    { sort s :=
        { toFun _ := id
          map_source j k h x := by
            change (((graduatedAlgebra A).sort s).str.dim j.val k.val h).source x =
              (dimensionLE ((graduatedAlgebra A).sort s).str _).source x
            rw [dimensionLE_of_lt _ _ (show j.val < k.val from h)]
          map_target j k h x := by
            change (((graduatedAlgebra A).sort s).str.dim j.val k.val h).target x =
              (dimensionLE ((graduatedAlgebra A).sort s).str _).target x
            rw [dimensionLE_of_lt _ _ (show j.val < k.val from h)]
          map_identity j k h x := by
            change (((graduatedAlgebra A).sort s).str.dim j.val k.val h).identity x =
              (dimensionLE ((graduatedAlgebra A).sort s).str _).identity x
            rw [dimensionLE_of_lt _ _ (show j.val < k.val from h)]
          map_comp j k h x y z hz := by
            change z ∈ (dimensionLE ((graduatedAlgebra A).sort s).str _).comp x y
            rw [dimensionLE_of_lt _ _ (show j.val < k.val from h)]
            exact hz }
      map_op _ _ _ := rfl }
    (fun _ _ => Function.bijective_id)

/-- Finite restriction of graduation is the successive induced finite transformation. -/
noncomputable def graduationRestrictionPartial :
    (heterogeneousOmegaTruncation sig n).transformed (graduatedAlgebra A).toPartialAlgebra ≅
      (Presentations.graduation n sig).transformed
        ((homogeneousOmegaTruncation sig n).transformed A.toPartialAlgebra) :=
  (heterogeneousDimensionRealization sig (omegaInclusion (n+1)).toOrderHom
    (orderEmbedding_saturating _) (graduatedAlgebra A)).symm ≪≫
    (Heterogeneous.modelFunctor ⋙ (Heterogeneous.specification (Fin (n+1)) sig).inclusion ⋙
      (Heterogeneous.epSignature (Fin (n+1)) sig).inclusion).mapIso
        ((finiteGraduationReindexIso A n).symm ≪≫ (finiteGraduationIso A n).symm) ≪≫
    eqToIso (Presentations.graduation_transformed n sig (omegaTruncatedAlgebra A n)).symm ≪≫
    (Presentations.graduation n sig).transformedFunctor.mapIso
      (homogeneousOmegaTruncationRealization sig n A)

/-- The inverse restriction comparison retains the scalar of a finite graduated cell. -/
theorem graduationRestrictionPartial_inv_val (p : Fin (n+1) × S) (x) :
    (((graduationRestrictionPartial A n).inv.toMap p x).val).val = x.val.val := by
  change ((eqToHom (Presentations.graduation_transformed n sig (omegaTruncatedAlgebra A n))).toMap p
    (((Presentations.graduation n sig).transformedFunctor.mapIso
      (homogeneousOmegaTruncationRealization sig n A)).inv.toMap p x)).val.val = x.val.val
  erw [Presentations.partial_eqToHom_toMap, cast_eq]
  exact homogeneousOmegaTruncationRealization_inv_val sig n A p.2 x.val

/-- The forward restriction comparison retains the scalar of the original cell. -/
theorem graduationRestrictionPartial_hom_val (p : Fin (n+1) × S) (x) :
    (((graduationRestrictionPartial A n).hom.toMap p x).val).val = x.val.val := by
  have hv := graduationRestrictionPartial_inv_val A n p
    ((graduationRestrictionPartial A n).hom.toMap p x)
  exact hv.symm.trans (congrArg (fun f : _ ⟶ _ => (f.toMap p x).val.val)
    (graduationRestrictionPartial A n).hom_inv_id)

end CategorialAlgebras.Omega
