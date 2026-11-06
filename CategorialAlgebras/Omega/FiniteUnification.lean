import CategorialAlgebras.Omega.Unification
import CategorialAlgebras.Omega.FiniteGraduation
import CategorialAlgebras.Presentations.UnificationModels

/-!
# Finite truncations of unification

The algebra in dimension $n$ embeds into unified cells by $x\mapsto[x]_n$.
Its image is exactly the cutoff-cell algebra. The finite induced unification
is related to the original dimensional carrier by its existing realization.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig) (n : ℕ)

/-- The stage carrier agrees with finite unification of the explicit restriction. -/
noncomputable def stageReindexIso : stageAlgebra B n ≅
    Presentations.unifiedAlgebra (reindexedAlgebra B (omegaInclusion (n+1)).toOrderHom
      (orderEmbedding_saturating _)) :=
  homogeneousIsoOfBijective
    { sort s :=
        { toFun := id
          map_source k x := by
            change (((B.sort s).str.dim k.val n k.isLt).identity
              (((B.sort s).str.dim k.val n k.isLt).source x)) =
                (dimensionLE (B.sort s).str k.isLt.le).identity
                  ((dimensionLE (B.sort s).str k.isLt.le).source x)
            rw [dimensionLE_of_lt _ _ k.isLt]
          map_target k x := by
            change (((B.sort s).str.dim k.val n k.isLt).identity
              (((B.sort s).str.dim k.val n k.isLt).target x)) =
                (dimensionLE (B.sort s).str k.isLt.le).identity
                  ((dimensionLE (B.sort s).str k.isLt.le).target x)
            rw [dimensionLE_of_lt _ _ k.isLt]
          map_comp k x y z hz := by
            change z ∈ (dimensionLE (B.sort s).str k.isLt.le).comp x y
            rw [dimensionLE_of_lt _ _ k.isLt]
            exact hz }
      map_op _ _ := rfl }
    (fun _ => Function.bijective_id)

/-- The stage algebra realizes the successive induced heterogeneous truncation and unification. -/
noncomputable def stageRealization : (stageAlgebra B n).toPartialAlgebra ≅
    (Presentations.unification n sig).transformed
      ((heterogeneousOmegaTruncation sig n).transformed B.toPartialAlgebra) :=
  (Homogeneous.modelFunctor ⋙ (Homogeneous.specification (Fin n) sig).inclusion ⋙
    (Homogeneous.epSignature (Fin n) sig).inclusion).mapIso (stageReindexIso B n) ≪≫
    Presentations.unificationRealization n sig _ ≪≫
    (Presentations.unification n sig).transformedFunctor.mapIso
      (heterogeneousDimensionRealization sig (omegaInclusion (n+1)).toOrderHom
        (orderEmbedding_saturating _) B)

/-- Realization of finite unification retains the original dimensional element. -/
@[simp] theorem stageRealization_hom_val (s : S) (x : B.carrier (n, s)) :
    (((stageRealization B n).hom.toMap s x).val).val = x := rfl

/-- The inverse finite realization also retains the original element. -/
theorem stageRealization_inv_val (s : S) (x) :
    (stageRealization B n).inv.toMap s x = x.val.val := by
  exact congrArg (fun f : _ ⟶ _ => (f.toMap s x).val.val) (stageRealization B n).inv_hom_id

/-- The stage injection, with its proof of belonging to the cutoff-cell algebra. -/
noncomputable def stageCutoffCell (s : S) (x : B.carrier (n, s)) :
    (omegaTruncatedAlgebra (unifiedAlgebra B) n).carrier s :=
  cutoffCell (unifiedAlgebra B) n s (cellIn B n s x) (cellIn_isCell B n s x)

/-- The stage injection is a bijection onto the cutoff cells. -/
theorem stageCutoffCell_bijective (s : S) : Function.Bijective (stageCutoffCell B n s) := by
  constructor
  · intro x y h
    exact cellIn_injective B n s (congrArg Subtype.val h)
  · intro x
    obtain ⟨y, hy⟩ := (unified_isCell_iff B n s x.val).mp
      (omegaTruncatedAlgebra_cell sig n (unifiedAlgebra B) s x)
    exact ⟨y, Subtype.ext hy⟩

/-- Insertion of a stage preserves the finite homogeneous operations. -/
noncomputable def stageCutoffHom : stageAlgebra B n ⟶ omegaTruncatedAlgebra (unifiedAlgebra B) n where
  sort s :=
    { toFun := stageCutoffCell B n s
      map_source k x := Subtype.ext ((unifiedSource_in B k s x).symm.trans
        (cutoff_source_val (unifiedAlgebra B) n k s (stageCutoffCell B n s x)).symm)
      map_target k x := Subtype.ext ((unifiedTarget_in B k s x).symm.trans
        (cutoff_target_val (unifiedAlgebra B) n k s (stageCutoffCell B n s x)).symm)
      map_comp k x y z hz := by
        apply (truncated_comp_mem sig (Nat.le_succ n)
          (omegaRestrictedAlgebra (unifiedAlgebra B) (n+1)) k s _ _ _).mpr
        exact (unifiedComp_mem B k s x y z).mpr hz }
  map_op σ x := Subtype.ext (unifiedBase_in B σ x).symm

/-- The $n$th dimensional carrier is isomorphic to the $n$-cells of unification. -/
noncomputable def stageCutoffIso : stageAlgebra B n ≅ omegaTruncatedAlgebra (unifiedAlgebra B) n :=
  homogeneousIsoOfBijective (stageCutoffHom B n) (stageCutoffCell_bijective B n)

/-- The finite unification-truncation comparison on exact induced partial algebras. -/
noncomputable def truncationUnificationPartial :
    (Presentations.unification n sig).transformed
      ((heterogeneousOmegaTruncation sig n).transformed B.toPartialAlgebra) ≅
    (homogeneousOmegaTruncation sig n).transformed (unifiedAlgebra B).toPartialAlgebra :=
  (stageRealization B n).symm ≪≫
    (Homogeneous.modelFunctor ⋙ (Homogeneous.specification (Fin n) sig).inclusion ⋙
      (Homogeneous.epSignature (Fin n) sig).inclusion).mapIso (stageCutoffIso B n) ≪≫
    homogeneousOmegaTruncationRealization sig n (unifiedAlgebra B)

/-- The finite comparison sends an original representative $x$ to its class $[x]_n$. -/
theorem truncationUnificationPartial_hom_val (s : S) (x) :
    ((truncationUnificationPartial B n).hom.toMap s x).val = cellIn B n s x.val.val := by
  change cellIn B n s ((stageRealization B n).inv.toMap s x) = _
  rw [stageRealization_inv_val]

end CategorialAlgebras.Omega
