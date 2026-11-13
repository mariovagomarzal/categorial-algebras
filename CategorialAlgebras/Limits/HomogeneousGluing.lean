import CategorialAlgebras.Limits.HomogeneousUnionLaws

/-!
# Categorical structures on the increasing union

Every finite tuple of cells lies in a sufficiently large finite stage. The
stage-independent operation formulas transfer category laws, compatibility,
and functoriality of the original operations to the union.
-/

universe u v w
namespace CategorialAlgebras.Limits
open CategoryTheory Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (homogeneousSystem.{u, v, w} sig).Family)

/-- The category structure in a single dimension of the increasing union. -/
noncomputable def homogeneousUnionDimension (k : ℕ) (s : S) :
    Homogeneous.CategoryStructure (HomogeneousUnion A s) where
  source := homogeneousUnionSource A k s
  target := homogeneousUnionTarget A k s
  comp := homogeneousUnionComp A k s
  source_source x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [homogeneousUnionSource_in A k' s]
    | erw [homogeneousUnionSource_in A k' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.dim k').source_source (ys 0))
  source_target x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [homogeneousUnionTarget_in A k' s]
    | erw [homogeneousUnionSource_in A k' s]
    | erw [homogeneousUnionTarget_in A k' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.dim k').source_target (ys 0))
  target_source x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [homogeneousUnionSource_in A k' s]
    | erw [homogeneousUnionTarget_in A k' s]
    | erw [homogeneousUnionSource_in A k' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.dim k').target_source (ys 0))
  target_target x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [homogeneousUnionTarget_in A k' s]
    | erw [homogeneousUnionTarget_in A k' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.dim k').target_target (ys 0))
  comp_dom x y := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 2 => s) ![x, y] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    have h1 : homogeneousUnionIn A n s (ys 1) = y := hy 1
    simp only [← h0, ← h1]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    rw [homogeneousUnionComp_in A k' s]
    change ((((homogeneousStage A n).sort s).str.dim k').comp (ys 0) (ys 1)).Dom ↔ _
    rw [Homogeneous.CategoryStructure.comp_dom,
      homogeneousUnionSource_in A k' s, homogeneousUnionTarget_in A k' s]
    exact (homogeneousUnionIn_injective A n s).eq_iff.symm
  source_comp x y z hz := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    have h1 : homogeneousUnionIn A n s (ys 1) = y := hy 1
    have h2 : homogeneousUnionIn A n s (ys 2) = z := hy 2
    simp only [← h0, ← h1, ← h2] at hz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    rw [homogeneousUnionComp_mem A k' s] at hz
    repeat' first
    | erw [homogeneousUnionSource_in A k' s]
    | erw [homogeneousUnionSource_in A k' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.dim k').source_comp _ _ _ hz)
  target_comp x y z hz := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    have h1 : homogeneousUnionIn A n s (ys 1) = y := hy 1
    have h2 : homogeneousUnionIn A n s (ys 2) = z := hy 2
    simp only [← h0, ← h1, ← h2] at hz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    rw [homogeneousUnionComp_mem A k' s] at hz
    repeat' first
    | erw [homogeneousUnionTarget_in A k' s]
    | erw [homogeneousUnionTarget_in A k' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.dim k').target_comp _ _ _ hz)
  comp_source x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [homogeneousUnionSource_in A k' s]
    rw [homogeneousUnionComp_mem A k' s]
    exact (((homogeneousStage A n).sort s).str.dim k').comp_source _
  target_comp_self x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [homogeneousUnionTarget_in A k' s]
    rw [homogeneousUnionComp_mem A k' s]
    exact (((homogeneousStage A n).sort s).str.dim k').target_comp_self _
  assoc x y z xy yz hxy hyz := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 5 => s) ![x, y, z, xy, yz] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    have h1 : homogeneousUnionIn A n s (ys 1) = y := hy 1
    have h2 : homogeneousUnionIn A n s (ys 2) = z := hy 2
    have h3 : homogeneousUnionIn A n s (ys 3) = xy := hy 3
    have h4 : homogeneousUnionIn A n s (ys 4) = yz := hy 4
    simp only [← h0, ← h1, ← h2, ← h3, ← h4] at hxy hyz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    rw [homogeneousUnionComp_mem A k' s] at hxy hyz
    obtain ⟨q, hq, hq'⟩ := (((homogeneousStage A n).sort s).str.dim k').assoc _ _ _ _ _ hxy hyz
    exact ⟨homogeneousUnionIn A n s q,
      (homogeneousUnionComp_mem A k' s _ _ _).mpr hq,
      (homogeneousUnionComp_mem A k' s _ _ _).mpr hq'⟩

/-- The structures on the increasing union are compatible in every increasing pair. -/
theorem homogeneousUnion_compatible {l k : ℕ} (h : l < k) (s : S) :
    Homogeneous.Compatible (homogeneousUnionDimension A l s) (homogeneousUnionDimension A k s) where
  source_source x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change homogeneousUnionSource A k s (homogeneousUnionSource A l s (homogeneousUnionIn A n s (ys 0))) =
      homogeneousUnionSource A l s (homogeneousUnionIn A n s (ys 0))
    repeat' first
    | erw [homogeneousUnionSource_in A l' s]
    | erw [homogeneousUnionSource_in A k' s]
    | erw [homogeneousUnionSource_in A l' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.compatible l' k' h).source_source _)
  target_target x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change homogeneousUnionTarget A k s (homogeneousUnionTarget A l s (homogeneousUnionIn A n s (ys 0))) =
      homogeneousUnionTarget A l s (homogeneousUnionIn A n s (ys 0))
    repeat' first
    | erw [homogeneousUnionTarget_in A l' s]
    | erw [homogeneousUnionTarget_in A k' s]
    | erw [homogeneousUnionTarget_in A l' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.compatible l' k' h).target_target _)
  source_source_low x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change homogeneousUnionSource A l s (homogeneousUnionSource A k s (homogeneousUnionIn A n s (ys 0))) =
      homogeneousUnionSource A l s (homogeneousUnionIn A n s (ys 0))
    repeat' first
    | erw [homogeneousUnionSource_in A k' s]
    | erw [homogeneousUnionSource_in A l' s]
    | erw [homogeneousUnionSource_in A l' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.compatible l' k' h).source_source_low _)
  target_target_low x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change homogeneousUnionTarget A l s (homogeneousUnionTarget A k s (homogeneousUnionIn A n s (ys 0))) =
      homogeneousUnionTarget A l s (homogeneousUnionIn A n s (ys 0))
    repeat' first
    | erw [homogeneousUnionTarget_in A k' s]
    | erw [homogeneousUnionTarget_in A l' s]
    | erw [homogeneousUnionTarget_in A l' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.compatible l' k' h).target_target_low _)
  source_target x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change homogeneousUnionSource A l s (homogeneousUnionTarget A k s (homogeneousUnionIn A n s (ys 0))) =
      homogeneousUnionSource A l s (homogeneousUnionIn A n s (ys 0))
    repeat' first
    | erw [homogeneousUnionTarget_in A k' s]
    | erw [homogeneousUnionSource_in A l' s]
    | erw [homogeneousUnionSource_in A l' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.compatible l' k' h).source_target _)
  target_source x := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change homogeneousUnionTarget A l s (homogeneousUnionSource A k s (homogeneousUnionIn A n s (ys 0))) =
      homogeneousUnionTarget A l s (homogeneousUnionIn A n s (ys 0))
    repeat' first
    | erw [homogeneousUnionSource_in A k' s]
    | erw [homogeneousUnionTarget_in A l' s]
    | erw [homogeneousUnionTarget_in A l' s]
    exact congrArg (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.compatible l' k' h).target_source _)
  source_comp x y z hz := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    have h1 : homogeneousUnionIn A n s (ys 1) = y := hy 1
    have h2 : homogeneousUnionIn A n s (ys 2) = z := hy 2
    simp only [← h0, ← h1, ← h2] at hz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change _ ∈ homogeneousUnionComp A l s _ _ at hz
    change homogeneousUnionSource A k s (homogeneousUnionIn A n s (ys 2)) ∈
      homogeneousUnionComp A l s (homogeneousUnionSource A k s (homogeneousUnionIn A n s (ys 0)))
        (homogeneousUnionSource A k s (homogeneousUnionIn A n s (ys 1)))
    rw [homogeneousUnionComp_mem A l' s] at hz
    repeat' first
    | erw [homogeneousUnionSource_in A k' s]
    | erw [homogeneousUnionSource_in A k' s]
    rw [homogeneousUnionComp_mem A l' s]
    exact (((homogeneousStage A n).sort s).str.compatible l' k' h).source_comp _ _ _ hz
  target_comp x y z hz := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    have h1 : homogeneousUnionIn A n s (ys 1) = y := hy 1
    have h2 : homogeneousUnionIn A n s (ys 2) = z := hy 2
    simp only [← h0, ← h1, ← h2] at hz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change _ ∈ homogeneousUnionComp A l s _ _ at hz
    change homogeneousUnionTarget A k s (homogeneousUnionIn A n s (ys 2)) ∈
      homogeneousUnionComp A l s (homogeneousUnionTarget A k s (homogeneousUnionIn A n s (ys 0)))
        (homogeneousUnionTarget A k s (homogeneousUnionIn A n s (ys 1)))
    rw [homogeneousUnionComp_mem A l' s] at hz
    repeat' first
    | erw [homogeneousUnionTarget_in A k' s]
    | erw [homogeneousUnionTarget_in A k' s]
    rw [homogeneousUnionComp_mem A l' s]
    exact (((homogeneousStage A n).sort s).str.compatible l' k' h).target_comp _ _ _ hz
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun _ : Fin 8 => s) ![x, y, z, t, xy, zt, xz, yt] (k + 1)
    have h0 : homogeneousUnionIn A n s (ys 0) = x := hy 0
    have h1 : homogeneousUnionIn A n s (ys 1) = y := hy 1
    have h2 : homogeneousUnionIn A n s (ys 2) = z := hy 2
    have h3 : homogeneousUnionIn A n s (ys 3) = t := hy 3
    have h4 : homogeneousUnionIn A n s (ys 4) = xy := hy 4
    have h5 : homogeneousUnionIn A n s (ys 5) = zt := hy 5
    have h6 : homogeneousUnionIn A n s (ys 6) = xz := hy 6
    have h7 : homogeneousUnionIn A n s (ys 7) = yt := hy 7
    simp only [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7] at hxy hzt hxz hyt ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change _ ∈ homogeneousUnionComp A l s _ _ at hxy hzt
    change _ ∈ homogeneousUnionComp A k s _ _ at hxz hyt
    rw [homogeneousUnionComp_mem A l' s] at hxy hzt
    rw [homogeneousUnionComp_mem A k' s] at hxz hyt
    obtain ⟨q, hq, hq'⟩ := (((homogeneousStage A n).sort s).str.compatible l' k' h).interchange
      _ _ _ _ _ _ _ _ hxy hzt hxz hyt
    exact ⟨homogeneousUnionIn A n s q,
      (homogeneousUnionComp_mem A k' s _ _ _).mpr hq,
      (homogeneousUnionComp_mem A l' s _ _ _).mpr hq'⟩

/-- The higher category on the increasing union at a sort. -/
noncomputable def homogeneousUnionSort (s : S) : Homogeneous.HigherCategory ℕ where
  carrier := HomogeneousUnion A s
  str.dim k := homogeneousUnionDimension A k s
  str.compatible _ _ h := homogeneousUnion_compatible A h s
/-- The original operations on the increasing union are higher functors. -/
noncomputable def homogeneousUnionAlgebra : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig where
  sort := homogeneousUnionSort A
  op {a} {s} σ :=
    { toFun := homogeneousUnionBase A σ
      map_source k x := by
        obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun j => a.get j) x (k + 1)
        have hx : (fun j => homogeneousUnionIn A n _ (ys j)) = x := funext hy
        rw [← hx]
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change homogeneousUnionBase A σ (fun j => homogeneousUnionSource A k _ (homogeneousUnionIn A n _ (ys j))) =
          homogeneousUnionSource A k s (homogeneousUnionBase A σ (fun j => homogeneousUnionIn A n _ (ys j)))
        have hs : (fun j => homogeneousUnionSource A k _ (homogeneousUnionIn A n _ (ys j))) =
            (fun j => homogeneousUnionIn A n _ ((((homogeneousStage A n).sort _).str.dim k').source (ys j))) := by
          funext j
          exact homogeneousUnionSource_in A k' _ (ys j)
        rw [hs, homogeneousUnionBase_in, homogeneousUnionBase_in]
        erw [homogeneousUnionSource_in A k' s]
        exact congrArg (homogeneousUnionIn A n s) (((homogeneousStage A n).op σ).map_source k' ys)
      map_target k x := by
        obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover A (fun j => a.get j) x (k + 1)
        have hx : (fun j => homogeneousUnionIn A n _ (ys j)) = x := funext hy
        rw [← hx]
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change homogeneousUnionBase A σ (fun j => homogeneousUnionTarget A k _ (homogeneousUnionIn A n _ (ys j))) =
          homogeneousUnionTarget A k s (homogeneousUnionBase A σ (fun j => homogeneousUnionIn A n _ (ys j)))
        have hs : (fun j => homogeneousUnionTarget A k _ (homogeneousUnionIn A n _ (ys j))) =
            (fun j => homogeneousUnionIn A n _ ((((homogeneousStage A n).sort _).str.dim k').target (ys j))) := by
          funext j
          exact homogeneousUnionTarget_in A k' _ (ys j)
        rw [hs, homogeneousUnionBase_in, homogeneousUnionBase_in]
        erw [homogeneousUnionTarget_in A k' s]
        exact congrArg (homogeneousUnionIn A n s) (((homogeneousStage A n).op σ).map_target k' ys)
      map_comp k x y z hz := by
        let xs : ∀ i : Fin 3 × Fin a.length, HomogeneousUnion A (a.get i.2) := fun i => ![x, y, z] i.1 i.2
        obtain ⟨n, hn, ys, hy⟩ := homogeneousUnion_cover_finite A (fun i : Fin 3 × Fin a.length => a.get i.2) xs (k+1)
        let x' : Word.Family (homogeneousStage A n).carrier a := fun j => ys (0, j)
        let y' : Word.Family (homogeneousStage A n).carrier a := fun j => ys (1, j)
        let z' : Word.Family (homogeneousStage A n).carrier a := fun j => ys (2, j)
        have hx : (fun j => homogeneousUnionIn A n _ (x' j)) = x := funext (fun j => hy (0, j))
        have hy' : (fun j => homogeneousUnionIn A n _ (y' j)) = y := funext (fun j => hy (1, j))
        have hz' : (fun j => homogeneousUnionIn A n _ (z' j)) = z := funext (fun j => hy (2, j))
        rw [← hx, ← hy', ← hz'] at hz ⊢
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change homogeneousUnionBase A σ _ ∈ homogeneousUnionComp A k s
          (homogeneousUnionBase A σ _) (homogeneousUnionBase A σ _)
        rw [homogeneousUnionBase_in, homogeneousUnionBase_in, homogeneousUnionBase_in,
          homogeneousUnionComp_mem A k' s]
        have hm : ∀ j, z' j ∈ (((homogeneousStage A n).sort (a.get j)).str.dim k').comp (x' j) (y' j) := by
          intro j
          exact (homogeneousUnionComp_mem A k' _ _ _ _).mp ((mem_partFamily _ _).mp hz j)
        exact ((homogeneousStage A n).op σ).map_comp k' x' y' z' ((mem_partFamily _ _).mpr hm) }

/-- The homogeneous union algebra expands to the exact explicit union operations. -/
theorem homogeneousUnionAlgebra_expansion :
    (homogeneousUnionAlgebra A).toPartialAlgebra = homogeneousUnionPartial A := by
  apply congrArg (PartialAlgebra.mk (HomogeneousUnion A))
  funext a s σ x
  cases σ <;> rfl

/-- The explicit union partial algebra satisfies all homogeneous model laws. -/
theorem homogeneousUnion_isModel :
    (Homogeneous.specification ℕ sig).IsModel (homogeneousUnionPartial A) := by
  rw [← homogeneousUnionAlgebra_expansion]
  exact ⟨Homogeneous.equations_isEPAlgebra (homogeneousUnionAlgebra A).satisfiesEquations,
    fun _ ⟨e, he⟩ => he ▸ (homogeneousUnionAlgebra A).satisfiesEquations e⟩

/-- The image of a finite stage in a later stage consists of cutoff cells. -/
theorem homogeneousStageInclusion_cell {m n : ℕ} (h : m < n) (s)
    (x : (A.obj m).obj.obj.carrier s) :
    ((homogeneousStage A n).sort s).str.IsCell ⟨m, h⟩ (homogeneousStageInclusion A h.le s x) := by
  have hx := ((A.transition h.le).inv.hom.hom.toMap s x).property
  have hh := (homogeneousTruncation_isCell_iff_model h.le (A.obj n).obj.obj
    ⟨(A.obj n).obj.property, (A.obj n).property⟩ s _).mp hx
  exact hh h

/-- Every finite-stage cell is fixed by its cutoff source in the union. -/
theorem homogeneousUnionIn_isCell (n : ℕ) (s) (x : (A.obj n).obj.obj.carrier s) :
    homogeneousUnionSource A n s (homogeneousUnionIn A n s x) = homogeneousUnionIn A n s x := by
  have he := homogeneousUnionIn_inclusion A (Nat.le_succ n) s x
  have hc := homogeneousStageInclusion_cell A (Nat.lt_succ_self n) s x
  calc
    _ = homogeneousUnionSource A n s
        (homogeneousUnionIn A (n+1) s (homogeneousStageInclusion A (Nat.le_succ n) s x)) := congrArg _ he
    _ = homogeneousUnionIn A (n+1) s (homogeneousStageInclusion A (Nat.le_succ n) s x) := by
      erw [homogeneousUnionSource_in A ⟨n, Nat.lt_succ_self n⟩ s]
      exact congrArg (homogeneousUnionIn A (n+1) s) hc
    _ = _ := he.symm

/-- Every cell of the union has finite dimension. -/
theorem homogeneousUnion_finite : Homogeneous.FiniteCells (homogeneousUnionPartial A) := by
  intro s x
  obtain ⟨n, y, rfl⟩ := homogeneousUnionIn_surjective A s x
  exact ⟨n, Part.mem_some_iff.mpr (homogeneousUnionIn_isCell A n s y).symm⟩

end CategorialAlgebras.Limits
