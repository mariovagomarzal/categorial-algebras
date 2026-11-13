import CategorialAlgebras.Limits.HomogeneousCarrier
import CategorialAlgebras.Limits.ModelTransport
import CategorialAlgebras.Limits.StageCoherence

/-!
# The embeddings of homogeneous finite stages

Each inverse transition embeds the lower algebra as the cells at its cutoff
in a higher stage. It preserves original operations, boundaries and all defined
compositions below that cutoff, and reflects those compositions.
-/

universe u v w
namespace CategorialAlgebras.Limits
open CategoryTheory Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (homogeneousSystem.{u, v, w} sig).Family)

/-- The recovered homogeneous stage has its original partial algebra. -/
noncomputable def homogeneousStageIso (n : ℕ) :
    (homogeneousStage A n).toPartialAlgebra ≅ (A.obj n).obj.obj :=
  eqToIso (Homogeneous.toPartialAlgebra_ofEquations _ _)

/-- The recovered-stage identification fixes elements. -/
@[simp] theorem homogeneousStageIso_hom (n : ℕ) (s) (x) :
    (homogeneousStageIso A n).hom.toMap s x = x :=
  fixedCarrier_eqToHom (Homogeneous.toPartialAlgebra_ofEquations _ _) s x

/-- The inverse recovered-stage identification fixes elements. -/
@[simp] theorem homogeneousStageIso_inv (n : ℕ) (s) (x) :
    (homogeneousStageIso A n).inv.toMap s x = x :=
  fixedCarrier_eqToHom (Homogeneous.toPartialAlgebra_ofEquations _ _).symm s x

/-- Restrict homogeneous dimensions while retaining all elements. -/
def finiteRestrictedAlgebra {m n : ℕ} (h : m ≤ n)
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) : Homogeneous.NCategorialAlgebra m sig where
  sort s := ⟨(B.sort s).carrier, (B.sort s).str.restrict (dimensionInclusion h)⟩
  op σ :=
    { toFun := (B.op σ).toFun
      map_source k x := (B.op σ).map_source (dimensionInclusion h k) x
      map_target k x := (B.op σ).map_target (dimensionInclusion h k) x
      map_comp k x y z hz := (B.op σ).map_comp (dimensionInclusion h k) x y z hz }

/-- Forget the cutoff-cell proof in an explicit finite truncation. -/
noncomputable def finiteTruncationInclusion {m n : ℕ} (h : m ≤ n)
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    Homogeneous.CategorialAlgebra.Hom (truncatedAlgebra h B) (finiteRestrictedAlgebra h B) where
  sort s :=
    { toFun := Subtype.val
      map_source k x := truncated_source_val sig h B k s x
      map_target k x := truncated_target_val sig h B k s x
      map_comp k x y z hz := (truncated_comp_mem sig h B k s x y z).mp hz }
  map_op _ _ := rfl

/-- A finite homogeneous stage embeds as a homomorphism into every later restriction. -/
noncomputable def homogeneousStageHom {m n : ℕ} (h : m ≤ n) :
    Homogeneous.CategorialAlgebra.Hom (homogeneousStage A m)
      (finiteRestrictedAlgebra h (homogeneousStage A n)) :=
  Homogeneous.CategorialAlgebra.Hom.ofPartialHom
    ((homogeneousStageIso A m).hom ≫ (A.transition h).inv.hom.hom ≫
      (homogeneousTruncation sig h).transformedHom (homogeneousStageIso A n).inv ≫
      eqToHom (homogeneousTruncation_transformed sig h (homogeneousStage A n)) ≫
      (finiteTruncationInclusion h (homogeneousStage A n)).toPartialHom)

/-- The structured stage embedding is the original inclusion on elements. -/
@[simp] theorem homogeneousStageHom_val {m n : ℕ} (h : m ≤ n) (s) (x) :
    ((homogeneousStageHom A h).sort s).toFun x = homogeneousStageInclusion A h s x := by
  change ((eqToHom (homogeneousTruncation_transformed sig h (homogeneousStage A n))).toMap s _).val = _
  erw [fixedCarrier_eqToHom]
  change (homogeneousStageIso A n).inv.toMap s
    (((A.transition h).inv.hom.hom.toMap s ((homogeneousStageIso A m).hom.toMap s x)).val) = _
  rw [homogeneousStageIso_inv, homogeneousStageIso_hom]
  rfl

/-- Stage embeddings preserve sources in their lower dimensions. -/
theorem homogeneousStageInclusion_source {m n : ℕ} (h : m ≤ n) (s) (k : Fin m) (x) :
    homogeneousStageInclusion A h s (((homogeneousStage A m).sort s).str.dim k |>.source x) =
      (((homogeneousStage A n).sort s).str.dim (dimensionInclusion h k)).source
        (homogeneousStageInclusion A h s x) := by
  have hh := ((homogeneousStageHom A h).sort s).map_source k x
  erw [homogeneousStageHom_val, homogeneousStageHom_val] at hh
  exact hh

/-- Stage embeddings preserve targets in their lower dimensions. -/
theorem homogeneousStageInclusion_target {m n : ℕ} (h : m ≤ n) (s) (k : Fin m) (x) :
    homogeneousStageInclusion A h s (((homogeneousStage A m).sort s).str.dim k |>.target x) =
      (((homogeneousStage A n).sort s).str.dim (dimensionInclusion h k)).target
        (homogeneousStageInclusion A h s x) := by
  have hh := ((homogeneousStageHom A h).sort s).map_target k x
  erw [homogeneousStageHom_val, homogeneousStageHom_val] at hh
  exact hh

/-- Stage embeddings preserve composition values in their lower dimensions. -/
theorem homogeneousStageInclusion_comp {m n : ℕ} (h : m ≤ n) (s) (k : Fin m) (x y z)
    (hz : z ∈ (((homogeneousStage A m).sort s).str.dim k).comp x y) :
    homogeneousStageInclusion A h s z ∈
      (((homogeneousStage A n).sort s).str.dim (dimensionInclusion h k)).comp
        (homogeneousStageInclusion A h s x) (homogeneousStageInclusion A h s y) := by
  have hh := ((homogeneousStageHom A h).sort s).map_comp k x y z hz
  simp only [homogeneousStageHom_val] at hh
  exact hh

/-- Stage embeddings preserve original operations, including nullary operations. -/
theorem homogeneousStageInclusion_op {m n : ℕ} (h : m ≤ n) {a s} (σ : sig a s) (x) :
    homogeneousStageInclusion A h s (((homogeneousStage A m).op σ).toFun x) =
      ((homogeneousStage A n).op σ).toFun (fun j => homogeneousStageInclusion A h _ (x j)) := by
  have hh := (homogeneousStageHom A h).map_op σ x
  simp only [homogeneousStageHom_val] at hh
  exact hh

/-- Within one finite stage the inclusion is identity. -/
@[simp] theorem homogeneousStageInclusion_self (n : ℕ) (s) (x) :
    homogeneousStageInclusion A (le_refl n) s x = x := by
  have he := congrArg (fun g : A.obj n ⟶ A.obj n => g.hom.hom.toMap s x)
    (A.transition (le_refl n)).inv_hom_id
  change (A.transition (le_refl n)).hom.hom.hom.toMap s
    ((A.transition (le_refl n)).inv.hom.hom.toMap s x) = x at he
  rw [A.identity n] at he
  exact (homogeneousIdentity_val sig n (A.obj n) s _).symm.trans he

/-- The finite-stage embeddings form a directed system. -/
theorem homogeneousStageInclusion_trans {m n p : ℕ} (h : m ≤ n) (k : n ≤ p) (s) (x) :
    homogeneousStageInclusion A k s (homogeneousStageInclusion A h s x) =
      homogeneousStageInclusion A (le_trans h k) s x := by
  have he := congrArg (fun g => (g.hom.hom.toMap s x).val) (A.inverse_coherence h k)
  change
    (((homogeneousTruncationModelsComp sig h k).hom.app (A.obj p)).hom.hom.toMap s
      (((homogeneousTruncationModels sig h).map (A.transition k).inv).hom.hom.toMap s
        ((A.transition h).inv.hom.hom.toMap s x))).val = _ at he
  have hv := homogeneousComposition_val sig h k (A.obj p) s
    (((homogeneousTruncationModels sig h).map (A.transition k).inv).hom.hom.toMap s
      ((A.transition h).inv.hom.hom.toMap s x))
  exact hv.symm.trans he

/-- Stage embeddings preserve and reflect composition values. -/
theorem homogeneousStageInclusion_comp_iff {m n : ℕ} (h : m ≤ n) (s) (k : Fin m) (x y z) :
    homogeneousStageInclusion A h s z ∈
      (((homogeneousStage A n).sort s).str.dim (dimensionInclusion h k)).comp
        (homogeneousStageInclusion A h s x) (homogeneousStageInclusion A h s y) ↔
      z ∈ (((homogeneousStage A m).sort s).str.dim k).comp x y := by
  constructor
  · intro hz
    have hd := (((homogeneousStage A n).sort s).str.dim _).comp_dom _ _ |>.mp hz.1
    rw [← homogeneousStageInclusion_source, ← homogeneousStageInclusion_target] at hd
    have hm := homogeneousStageInclusion_injective A h s hd
    have hp := (((homogeneousStage A m).sort s).str.dim k).comp_dom x y |>.mpr hm
    have hq := homogeneousStageInclusion_comp A h s k x y _ (Part.get_mem hp)
    have he := homogeneousStageInclusion_injective A h s (Part.mem_unique hq hz)
    exact he ▸ Part.get_mem hp
  · exact homogeneousStageInclusion_comp A h s k x y z

end CategorialAlgebras.Limits
