import CategorialAlgebras.Limits.HeterogeneousCarrier
import CategorialAlgebras.Limits.ModelTransport
import CategorialAlgebras.Limits.StageCoherence

/-!
# Coherent transports between heterogeneous stages

Inverse transition isomorphisms identify each lower-dimensional carrier with
its copy in every later stage. These transports preserve all categorical and
original operations and compose coherently.
-/

universe u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions Presentations

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (heterogeneousSystem.{u, v, w} sig).Family)

/-- Recovering a finite stage gives its original partial algebra. -/
noncomputable def heterogeneousStageIso (n : ℕ) :
    (heterogeneousStage A n).toPartialAlgebra ≅ (A.obj n).obj.obj :=
  eqToIso (Heterogeneous.toPartialAlgebra_ofEquations _ _)

/-- The recovered-stage identification fixes elements. -/
@[simp] theorem heterogeneousStageIso_hom (n : ℕ) (s) (x) :
    (heterogeneousStageIso A n).hom.toMap s x = x :=
  fixedCarrier_eqToHom (Heterogeneous.toPartialAlgebra_ofEquations _ _) s x

/-- The inverse recovered-stage identification fixes elements. -/
@[simp] theorem heterogeneousStageIso_inv (n : ℕ) (s) (x) :
    (heterogeneousStageIso A n).inv.toMap s x = x :=
  fixedCarrier_eqToHom (Heterogeneous.toPartialAlgebra_ofEquations _ _).symm s x

/-- Transport an arbitrary finite dimension to a later stage. -/
noncomputable def heterogeneousStageMap {m n : ℕ} (h : m ≤ n)
    (j : Fin (m + 1)) (s : S) (x : (A.obj m).obj.obj.carrier (j, s)) :
    (A.obj n).obj.obj.carrier (cellInclusion h j, s) :=
  ((A.transition h).inv.hom.hom.toMap (j, s) x).val

/-- The inverse transition, realized as a homomorphism on the original carriers. -/
noncomputable def heterogeneousStageHom {m n : ℕ} (h : m ≤ n) :
    Heterogeneous.CategorialAlgebra.Hom (heterogeneousStage A m)
      (reindexedAlgebra (heterogeneousStage A n) (cellInclusion h).toOrderHom
        (orderEmbedding_saturating _)) :=
  Heterogeneous.CategorialAlgebra.Hom.ofPartialHom
    ((heterogeneousStageIso A m).hom ≫ (A.transition h).inv.hom.hom ≫
      (heterogeneousTruncation sig h).transformedHom (heterogeneousStageIso A n).inv ≫
      (heterogeneousDimensionRealization sig (cellInclusion h).toOrderHom
        (orderEmbedding_saturating _) (heterogeneousStage A n)).inv)

/-- The stage homomorphism has the underlying transition transport. -/
@[simp] theorem heterogeneousStageHom_val {m n : ℕ} (h : m ≤ n)
    (j : Fin (m + 1)) (s : S) (x : (A.obj m).obj.obj.carrier (j, s)) :
    ((heterogeneousStageHom A h).sort s).toFun j x = heterogeneousStageMap A h j s x := by
  change (heterogeneousDimensionRealization sig (cellInclusion h).toOrderHom _ _).inv.toMap (j, s) _ = _
  erw [dimensionRealization_inv]
  change (heterogeneousStageIso A n).inv.toMap _
    (((A.transition h).inv.hom.hom.toMap (j, s) ((heterogeneousStageIso A m).hom.toMap (j, s) x)).val) = _
  rw [heterogeneousStageIso_inv, heterogeneousStageIso_hom]
  rfl

/-- Strict pairs in a finite restriction retain their original structure. -/
theorem stageReindexed_dim {m n : ℕ} (h : m ≤ n) (s : S)
    (j k : Fin (m + 1)) (hk : j < k) :
    (((reindexedAlgebra (heterogeneousStage A n) (cellInclusion h).toOrderHom
      (orderEmbedding_saturating _)).sort s).str.dim j k hk) =
      ((heterogeneousStage A n).sort s).str.dim (cellInclusion h j) (cellInclusion h k) hk := by
  change dimensionLE ((heterogeneousStage A n).sort s).str _ = _
  exact dimensionLE_of_lt _ _ (show cellInclusion h j < cellInclusion h k from hk)

/-- Finite-stage transports preserve sources. -/
theorem heterogeneousStageMap_source {m n : ℕ} (h : m ≤ n) (s : S)
    (j k : Fin (m + 1)) (hk : j < k) (x) :
    heterogeneousStageMap A h j s ((((heterogeneousStage A m).sort s).str.dim j k hk).source x) =
      (((heterogeneousStage A n).sort s).str.dim (cellInclusion h j) (cellInclusion h k) hk).source
        (heterogeneousStageMap A h k s x) := by
  have hh := ((heterogeneousStageHom A h).sort s).map_source j k hk x
  rw [stageReindexed_dim] at hh
  erw [heterogeneousStageHom_val, heterogeneousStageHom_val] at hh
  exact hh

/-- Finite-stage transports preserve targets. -/
theorem heterogeneousStageMap_target {m n : ℕ} (h : m ≤ n) (s : S)
    (j k : Fin (m + 1)) (hk : j < k) (x) :
    heterogeneousStageMap A h j s ((((heterogeneousStage A m).sort s).str.dim j k hk).target x) =
      (((heterogeneousStage A n).sort s).str.dim (cellInclusion h j) (cellInclusion h k) hk).target
        (heterogeneousStageMap A h k s x) := by
  have hh := ((heterogeneousStageHom A h).sort s).map_target j k hk x
  rw [stageReindexed_dim] at hh
  erw [heterogeneousStageHom_val, heterogeneousStageHom_val] at hh
  exact hh

/-- Finite-stage transports preserve identities. -/
theorem heterogeneousStageMap_identity {m n : ℕ} (h : m ≤ n) (s : S)
    (j k : Fin (m + 1)) (hk : j < k) (x) :
    heterogeneousStageMap A h k s ((((heterogeneousStage A m).sort s).str.dim j k hk).identity x) =
      (((heterogeneousStage A n).sort s).str.dim (cellInclusion h j) (cellInclusion h k) hk).identity
        (heterogeneousStageMap A h j s x) := by
  have hh := ((heterogeneousStageHom A h).sort s).map_identity j k hk x
  rw [stageReindexed_dim] at hh
  erw [heterogeneousStageHom_val, heterogeneousStageHom_val] at hh
  exact hh

/-- Finite-stage transports preserve defined composition values. -/
theorem heterogeneousStageMap_comp {m n : ℕ} (h : m ≤ n) (s : S)
    (j k : Fin (m + 1)) (hk : j < k) (x y z)
    (hz : z ∈ (((heterogeneousStage A m).sort s).str.dim j k hk).comp x y) :
    heterogeneousStageMap A h k s z ∈
      (((heterogeneousStage A n).sort s).str.dim (cellInclusion h j) (cellInclusion h k) hk).comp
        (heterogeneousStageMap A h k s x) (heterogeneousStageMap A h k s y) := by
  have hh := ((heterogeneousStageHom A h).sort s).map_comp j k hk x y z hz
  rw [stageReindexed_dim] at hh
  simp only [heterogeneousStageHom_val] at hh
  exact hh

/-- Finite-stage transports preserve every original operation. -/
theorem heterogeneousStageMap_op {m n : ℕ} (h : m ≤ n) {a s} (σ : sig a s)
    (j : Fin (m + 1)) (x) :
    heterogeneousStageMap A h j s (((heterogeneousStage A m).op σ).toFun j x) =
      ((heterogeneousStage A n).op σ).toFun (cellInclusion h j)
        (fun q => heterogeneousStageMap A h j _ (x q)) := by
  have hh := (heterogeneousStageHom A h).map_op σ j x
  change _ = ((heterogeneousStage A n).op σ).toFun (cellInclusion h j) _ at hh
  simp only [heterogeneousStageHom_val] at hh
  exact hh
/-- Stage transports within one stage are identity. -/
@[simp] theorem heterogeneousStageMap_self (n : ℕ) (j : Fin (n + 1)) (s : S) (x) :
    heterogeneousStageMap A (le_refl n) j s x = x := by
  have he := congrArg (fun g : A.obj n ⟶ A.obj n => g.hom.hom.toMap (j, s) x)
    (A.transition (le_refl n)).inv_hom_id
  change (A.transition (le_refl n)).hom.hom.hom.toMap (j, s)
    ((A.transition (le_refl n)).inv.hom.hom.toMap (j, s) x) = x at he
  rw [A.identity n] at he
  exact (eq_of_heq (heterogeneousIdentity_heq sig n (A.obj n) (j, s) _)).symm.trans he

/-- Stage transports compose without changing the underlying cell. -/
theorem heterogeneousStageMap_trans {m n p : ℕ} (h : m ≤ n) (k : n ≤ p)
    (j : Fin (m + 1)) (s : S) (x) :
    heterogeneousStageMap A k (cellInclusion h j) s (heterogeneousStageMap A h j s x) =
      heterogeneousStageMap A (le_trans h k) j s x := by
  have he := congrArg (fun g => (g.hom.hom.toMap (j, s) x).val) (A.inverse_coherence h k)
  change
    (((heterogeneousTruncationModelsComp sig h k).hom.app (A.obj p)).hom.hom.toMap (j, s)
      (((heterogeneousTruncationModels sig h).map (A.transition k).inv).hom.hom.toMap (j, s)
        ((A.transition h).inv.hom.hom.toMap (j, s) x))).val = _ at he
  have hv := eq_of_heq (heterogeneousComposition_heq sig h k (A.obj p) (j, s)
    (((heterogeneousTruncationModels sig h).map (A.transition k).inv).hom.hom.toMap (j, s)
      ((A.transition h).inv.hom.hom.toMap (j, s) x)))
  exact hv.symm.trans he

/-- Every stage transport at a retained dimension is bijective. -/
theorem heterogeneousStageMap_bijective {m n : ℕ} (h : m ≤ n)
    (j : Fin (m + 1)) (s : S) : Function.Bijective (heterogeneousStageMap A h j s) := by
  let e := (A.transition h)
  have he (z) : e.hom.hom.hom.toMap (j, s) (e.inv.hom.hom.toMap (j, s) z) = z :=
    congrArg (fun g : A.obj m ⟶ A.obj m => g.hom.hom.toMap (j, s) z) e.inv_hom_id
  constructor
  · intro x y hh
    exact (he x).symm.trans ((congrArg (e.hom.hom.hom.toMap (j, s)) (Subtype.ext hh)).trans (he y))
  · intro x
    let z : ((heterogeneousTruncationModels sig h).obj (A.obj n)).obj.obj.carrier (j, s) :=
      ⟨x, heterogeneousDimension_isCell sig (cellInclusion h).toOrderHom (A.obj n).obj.obj (j, s) x⟩
    refine ⟨e.hom.hom.hom.toMap (j, s) z, ?_⟩
    exact congrArg (fun g => (g.hom.hom.toMap (j, s) z).val) e.hom_inv_id

/-- The diagonal-to-stage chart is the top-dimensional stage transport. -/
theorem heterogeneousStageUp_eq {m n : ℕ} (h : m ≤ n) (s : S) (x) :
    heterogeneousStageUp A h s x = heterogeneousStageMap A h (Fin.last m) s x := rfl

/-- At its own level the diagonal chart is identity. -/
@[simp] theorem heterogeneousStageUp_self (n : ℕ) (s : S) (x) :
    heterogeneousStageUp A (le_refl n) s x = x := heterogeneousStageMap_self A n _ s x
/-- The diagonal charts commute with every later-stage transport. -/
theorem heterogeneousStageUp_trans {d m n : ℕ} (hd : d ≤ m) (h : m ≤ n) (s : S) (x) :
    heterogeneousStageMap A h ⟨d, Nat.lt_succ_of_le hd⟩ s (heterogeneousStageUp A hd s x) =
      heterogeneousStageUp A (le_trans hd h) s x :=
  heterogeneousStageMap_trans A hd h (Fin.last d) s x

/-- Finite-stage transports preserve and reflect all composition values. -/
theorem heterogeneousStageMap_comp_iff {m n : ℕ} (h : m ≤ n) (s : S)
    (j k : Fin (m + 1)) (hk : j < k) (x y z) :
    heterogeneousStageMap A h k s z ∈
      (((heterogeneousStage A n).sort s).str.dim (cellInclusion h j) (cellInclusion h k) hk).comp
        (heterogeneousStageMap A h k s x) (heterogeneousStageMap A h k s y) ↔
      z ∈ (((heterogeneousStage A m).sort s).str.dim j k hk).comp x y := by
  constructor
  · intro hz
    have hd := (((heterogeneousStage A n).sort s).str.dim _ _ hk).comp_dom _ _ |>.mp hz.1
    rw [← heterogeneousStageMap_source, ← heterogeneousStageMap_target] at hd
    have hm := (heterogeneousStageMap_bijective A h j s).1 hd
    have hp := (((heterogeneousStage A m).sort s).str.dim j k hk).comp_dom x y |>.mpr hm
    have hq := heterogeneousStageMap_comp A h s j k hk x y _ (Part.get_mem hp)
    have he := (heterogeneousStageMap_bijective A h k s).1 (Part.mem_unique hq hz)
    exact he ▸ Part.get_mem hp
  · exact heterogeneousStageMap_comp A h s j k hk x y z

end CategorialAlgebras.Limits
