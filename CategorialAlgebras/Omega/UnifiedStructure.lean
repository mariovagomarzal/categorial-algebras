import CategorialAlgebras.Omega.OperationLaws

/-!
# Categorical structures on the increasing union

Every finite tuple of cells lies in a sufficiently large finite stage. The
stage-independent operation formulas transfer category laws, compatibility,
and functoriality of the original operations to the union.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {S : Type u} {sig : Signature.{u, v} S}
variable (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)

/-- The category structure in a single dimension of the increasing union. -/
noncomputable def unifiedDimension (k : ℕ) (s : S) :
    Homogeneous.CategoryStructure (Cell B s) where
  source := unifiedSource B k s
  target := unifiedTarget B k s
  comp := unifiedComp B k s
  source_source x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [unifiedSource_in B k' s]
    | erw [unifiedSource_in B k' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.dim k').source_source (ys 0))
  source_target x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [unifiedTarget_in B k' s]
    | erw [unifiedSource_in B k' s]
    | erw [unifiedTarget_in B k' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.dim k').source_target (ys 0))
  target_source x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [unifiedSource_in B k' s]
    | erw [unifiedTarget_in B k' s]
    | erw [unifiedSource_in B k' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.dim k').target_source (ys 0))
  target_target x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [unifiedTarget_in B k' s]
    | erw [unifiedTarget_in B k' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.dim k').target_target (ys 0))
  comp_dom x y := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 2 => s) ![x, y] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    have h1 : cellIn B n s (ys 1) = y := hy 1
    simp only [← h0, ← h1]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    rw [unifiedComp_in B k' s]
    change ((((stageAlgebra B n).sort s).str.dim k').comp (ys 0) (ys 1)).Dom ↔ _
    rw [Homogeneous.CategoryStructure.comp_dom,
      unifiedSource_in B k' s, unifiedTarget_in B k' s]
    exact (cellIn_injective B n s).eq_iff.symm
  source_comp x y z hz := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    have h1 : cellIn B n s (ys 1) = y := hy 1
    have h2 : cellIn B n s (ys 2) = z := hy 2
    simp only [← h0, ← h1, ← h2] at hz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    rw [unifiedComp_mem B k' s] at hz
    repeat' first
    | erw [unifiedSource_in B k' s]
    | erw [unifiedSource_in B k' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.dim k').source_comp _ _ _ hz)
  target_comp x y z hz := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    have h1 : cellIn B n s (ys 1) = y := hy 1
    have h2 : cellIn B n s (ys 2) = z := hy 2
    simp only [← h0, ← h1, ← h2] at hz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    rw [unifiedComp_mem B k' s] at hz
    repeat' first
    | erw [unifiedTarget_in B k' s]
    | erw [unifiedTarget_in B k' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.dim k').target_comp _ _ _ hz)
  comp_source x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [unifiedSource_in B k' s]
    rw [unifiedComp_mem B k' s]
    exact (((stageAlgebra B n).sort s).str.dim k').comp_source _
  target_comp_self x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    repeat' first
    | erw [unifiedTarget_in B k' s]
    rw [unifiedComp_mem B k' s]
    exact (((stageAlgebra B n).sort s).str.dim k').target_comp_self _
  assoc x y z xy yz hxy hyz := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 5 => s) ![x, y, z, xy, yz] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    have h1 : cellIn B n s (ys 1) = y := hy 1
    have h2 : cellIn B n s (ys 2) = z := hy 2
    have h3 : cellIn B n s (ys 3) = xy := hy 3
    have h4 : cellIn B n s (ys 4) = yz := hy 4
    simp only [← h0, ← h1, ← h2, ← h3, ← h4] at hxy hyz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    rw [unifiedComp_mem B k' s] at hxy hyz
    obtain ⟨q, hq, hq'⟩ := (((stageAlgebra B n).sort s).str.dim k').assoc _ _ _ _ _ hxy hyz
    exact ⟨cellIn B n s q,
      (unifiedComp_mem B k' s _ _ _).mpr hq,
      (unifiedComp_mem B k' s _ _ _).mpr hq'⟩

/-- The structures on the increasing union are compatible in every increasing pair. -/
theorem unified_compatible {l k : ℕ} (h : l < k) (s : S) :
    Homogeneous.Compatible (unifiedDimension B l s) (unifiedDimension B k s) where
  source_source x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change unifiedSource B k s (unifiedSource B l s (cellIn B n s (ys 0))) =
      unifiedSource B l s (cellIn B n s (ys 0))
    repeat' first
    | erw [unifiedSource_in B l' s]
    | erw [unifiedSource_in B k' s]
    | erw [unifiedSource_in B l' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.compatible l' k' h).source_source _)
  target_target x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change unifiedTarget B k s (unifiedTarget B l s (cellIn B n s (ys 0))) =
      unifiedTarget B l s (cellIn B n s (ys 0))
    repeat' first
    | erw [unifiedTarget_in B l' s]
    | erw [unifiedTarget_in B k' s]
    | erw [unifiedTarget_in B l' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.compatible l' k' h).target_target _)
  source_source_low x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change unifiedSource B l s (unifiedSource B k s (cellIn B n s (ys 0))) =
      unifiedSource B l s (cellIn B n s (ys 0))
    repeat' first
    | erw [unifiedSource_in B k' s]
    | erw [unifiedSource_in B l' s]
    | erw [unifiedSource_in B l' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.compatible l' k' h).source_source_low _)
  target_target_low x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change unifiedTarget B l s (unifiedTarget B k s (cellIn B n s (ys 0))) =
      unifiedTarget B l s (cellIn B n s (ys 0))
    repeat' first
    | erw [unifiedTarget_in B k' s]
    | erw [unifiedTarget_in B l' s]
    | erw [unifiedTarget_in B l' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.compatible l' k' h).target_target_low _)
  source_target x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change unifiedSource B l s (unifiedTarget B k s (cellIn B n s (ys 0))) =
      unifiedSource B l s (cellIn B n s (ys 0))
    repeat' first
    | erw [unifiedTarget_in B k' s]
    | erw [unifiedSource_in B l' s]
    | erw [unifiedSource_in B l' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.compatible l' k' h).source_target _)
  target_source x := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    simp only [← h0]
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change unifiedTarget B l s (unifiedSource B k s (cellIn B n s (ys 0))) =
      unifiedTarget B l s (cellIn B n s (ys 0))
    repeat' first
    | erw [unifiedSource_in B k' s]
    | erw [unifiedTarget_in B l' s]
    | erw [unifiedTarget_in B l' s]
    exact congrArg (cellIn B n s) ((((stageAlgebra B n).sort s).str.compatible l' k' h).target_source _)
  source_comp x y z hz := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    have h1 : cellIn B n s (ys 1) = y := hy 1
    have h2 : cellIn B n s (ys 2) = z := hy 2
    simp only [← h0, ← h1, ← h2] at hz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change _ ∈ unifiedComp B l s _ _ at hz
    change unifiedSource B k s (cellIn B n s (ys 2)) ∈
      unifiedComp B l s (unifiedSource B k s (cellIn B n s (ys 0)))
        (unifiedSource B k s (cellIn B n s (ys 1)))
    rw [unifiedComp_mem B l' s] at hz
    repeat' first
    | erw [unifiedSource_in B k' s]
    | erw [unifiedSource_in B k' s]
    rw [unifiedComp_mem B l' s]
    exact (((stageAlgebra B n).sort s).str.compatible l' k' h).source_comp _ _ _ hz
  target_comp x y z hz := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    have h1 : cellIn B n s (ys 1) = y := hy 1
    have h2 : cellIn B n s (ys 2) = z := hy 2
    simp only [← h0, ← h1, ← h2] at hz ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change _ ∈ unifiedComp B l s _ _ at hz
    change unifiedTarget B k s (cellIn B n s (ys 2)) ∈
      unifiedComp B l s (unifiedTarget B k s (cellIn B n s (ys 0)))
        (unifiedTarget B k s (cellIn B n s (ys 1)))
    rw [unifiedComp_mem B l' s] at hz
    repeat' first
    | erw [unifiedTarget_in B k' s]
    | erw [unifiedTarget_in B k' s]
    rw [unifiedComp_mem B l' s]
    exact (((stageAlgebra B n).sort s).str.compatible l' k' h).target_comp _ _ _ hz
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun _ : Fin 8 => s) ![x, y, z, t, xy, zt, xz, yt] (k + 1)
    have h0 : cellIn B n s (ys 0) = x := hy 0
    have h1 : cellIn B n s (ys 1) = y := hy 1
    have h2 : cellIn B n s (ys 2) = z := hy 2
    have h3 : cellIn B n s (ys 3) = t := hy 3
    have h4 : cellIn B n s (ys 4) = xy := hy 4
    have h5 : cellIn B n s (ys 5) = zt := hy 5
    have h6 : cellIn B n s (ys 6) = xz := hy 6
    have h7 : cellIn B n s (ys 7) = yt := hy 7
    simp only [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7] at hxy hzt hxz hyt ⊢
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    let l' : Fin n := ⟨l, lt_trans h k'.isLt⟩
    change _ ∈ unifiedComp B l s _ _ at hxy hzt
    change _ ∈ unifiedComp B k s _ _ at hxz hyt
    rw [unifiedComp_mem B l' s] at hxy hzt
    rw [unifiedComp_mem B k' s] at hxz hyt
    obtain ⟨q, hq, hq'⟩ := (((stageAlgebra B n).sort s).str.compatible l' k' h).interchange
      _ _ _ _ _ _ _ _ hxy hzt hxz hyt
    exact ⟨cellIn B n s q,
      (unifiedComp_mem B k' s _ _ _).mpr hq,
      (unifiedComp_mem B l' s _ _ _).mpr hq'⟩

/-- The higher category on the increasing union at a sort. -/
noncomputable def unifiedSort (s : S) : Homogeneous.HigherCategory ℕ where
  carrier := Cell B s
  str.dim k := unifiedDimension B k s
  str.compatible _ _ h := unified_compatible B h s
/-- The original operations on the increasing union are higher functors. -/
noncomputable def unifiedAlgebra : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig where
  sort := unifiedSort B
  op {a} {s} σ :=
    { toFun := unifiedBase B σ
      map_source k x := by
        obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun j => a.get j) x (k + 1)
        have hx : (fun j => cellIn B n _ (ys j)) = x := funext hy
        rw [← hx]
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change unifiedBase B σ (fun j => unifiedSource B k _ (cellIn B n _ (ys j))) =
          unifiedSource B k s (unifiedBase B σ (fun j => cellIn B n _ (ys j)))
        have hs : (fun j => unifiedSource B k _ (cellIn B n _ (ys j))) =
            (fun j => cellIn B n _ ((((stageAlgebra B n).sort _).str.dim k').source (ys j))) := by
          funext j
          exact unifiedSource_in B k' _ (ys j)
        rw [hs, unifiedBase_in, unifiedBase_in]
        erw [unifiedSource_in B k' s]
        exact congrArg (cellIn B n s) (((stageAlgebra B n).op σ).map_source k' ys)
      map_target k x := by
        obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun j => a.get j) x (k + 1)
        have hx : (fun j => cellIn B n _ (ys j)) = x := funext hy
        rw [← hx]
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change unifiedBase B σ (fun j => unifiedTarget B k _ (cellIn B n _ (ys j))) =
          unifiedTarget B k s (unifiedBase B σ (fun j => cellIn B n _ (ys j)))
        have hs : (fun j => unifiedTarget B k _ (cellIn B n _ (ys j))) =
            (fun j => cellIn B n _ ((((stageAlgebra B n).sort _).str.dim k').target (ys j))) := by
          funext j
          exact unifiedTarget_in B k' _ (ys j)
        rw [hs, unifiedBase_in, unifiedBase_in]
        erw [unifiedTarget_in B k' s]
        exact congrArg (cellIn B n s) (((stageAlgebra B n).op σ).map_target k' ys)
      map_comp k x y z hz := by
        let xs : ∀ i : Fin 3 × Fin a.length, Cell B (a.get i.2) := fun i => ![x, y, z] i.1 i.2
        obtain ⟨n, hn, ys, hy⟩ := cell_cover B (fun i : Fin 3 × Fin a.length => a.get i.2) xs (k+1)
        let x' : Word.Family (stageAlgebra B n).carrier a := fun j => ys (0, j)
        let y' : Word.Family (stageAlgebra B n).carrier a := fun j => ys (1, j)
        let z' : Word.Family (stageAlgebra B n).carrier a := fun j => ys (2, j)
        have hx : (fun j => cellIn B n _ (x' j)) = x := funext (fun j => hy (0, j))
        have hy' : (fun j => cellIn B n _ (y' j)) = y := funext (fun j => hy (1, j))
        have hz' : (fun j => cellIn B n _ (z' j)) = z := funext (fun j => hy (2, j))
        rw [← hx, ← hy', ← hz'] at hz ⊢
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change unifiedBase B σ _ ∈ unifiedComp B k s
          (unifiedBase B σ _) (unifiedBase B σ _)
        rw [unifiedBase_in, unifiedBase_in, unifiedBase_in,
          unifiedComp_mem B k' s]
        have hm : ∀ j, z' j ∈ (((stageAlgebra B n).sort (a.get j)).str.dim k').comp (x' j) (y' j) := by
          intro j
          exact (unifiedComp_mem B k' _ _ _ _).mp ((mem_partFamily _ _).mp hz j)
        exact ((stageAlgebra B n).op σ).map_comp k' x' y' z' ((mem_partFamily _ _).mpr hm) }

/-- The homogeneous union algebra expands to the exact explicit union operations. -/
theorem unifiedAlgebra_expansion :
    (unifiedAlgebra B).toPartialAlgebra = unifiedPartial B := by
  apply congrArg (PartialAlgebra.mk (Cell B))
  funext a s σ x
  cases σ <;> rfl

/-- The explicit union partial algebra satisfies all homogeneous model laws. -/
theorem unified_isModel :
    (Homogeneous.specification ℕ sig).IsModel (unifiedPartial B) := by
  rw [← unifiedAlgebra_expansion]
  exact ⟨Homogeneous.equations_isEPAlgebra (unifiedAlgebra B).satisfiesEquations,
    fun _ ⟨e, he⟩ => he ▸ (unifiedAlgebra B).satisfiesEquations e⟩

end CategorialAlgebras.Omega
