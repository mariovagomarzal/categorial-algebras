import CategorialAlgebras.Omega.Operations

/-!
# Independence of unified operations from representatives

The same operations, including their exact partial domains, can be computed
in any common sufficiently large dimension.
-/

universe u v w
namespace CategorialAlgebras.Omega
open Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)

/-- A chosen representative, raised to a common stage, agrees with every other representative there. -/
theorem cellAt_eq {m n : ℕ} (h : m ≤ n) (s) (x : B.carrier (m, s))
    (hn : (Quotient.out (cellIn B m s x)).1 ≤ n) :
    cellAt B s (cellIn B m s x) n hn = inclusion B h s x :=
  cellIn_eq_at B hn h s _ x (Quotient.out_eq _)

/-- Moving a representative to a later stage does not change its image in the union. -/
theorem cellIn_comp {m n : ℕ} (h : m ≤ n) (s) :
    (cellIn B n s) ∘ (inclusion B h s) = cellIn B m s := by
  funext x
  exact (cellIn_raise B h s x).symm

/-- Stage inclusions commute with the whole partial composition, including its domain. -/
theorem inclusion_comp_map {m n : ℕ} (h : m ≤ n) (s) (k : Fin m) (x y) :
    Part.map (inclusion B h s) ((((stageAlgebra B m).sort s).str.dim k).comp x y) =
      (((stageAlgebra B n).sort s).str.dim (dimensionInclusion h k)).comp
        (inclusion B h s x) (inclusion B h s y) := by
  apply Part.ext
  intro z
  constructor
  · intro hz
    obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff _).mp hz
    exact inclusion_comp B h s k x y q hq
  · intro hz
    have hd := (((stageAlgebra B n).sort s).str.dim _).comp_dom _ _ |>.mp hz.1
    change (((stageAlgebra B n).sort s).str.dim ⟨k.val, lt_of_lt_of_le k.isLt h⟩).source
      (inclusion B h s x) =
        (((stageAlgebra B n).sort s).str.dim ⟨k.val, lt_of_lt_of_le k.isLt h⟩).target
          (inclusion B h s y) at hd
    rw [← inclusion_source, ← inclusion_target] at hd
    have hp := (((stageAlgebra B m).sort s).str.dim k).comp_dom x y |>.mpr
      (inclusion_injective B h s hd)
    have hq := inclusion_comp B h s k x y _ (Part.get_mem hp)
    exact (Part.mem_map_iff _).mpr ⟨_, Part.get_mem hp, Part.mem_unique hq hz⟩

/-- Raising a chosen representative agrees with its direct raising to the later stage. -/
theorem cellAt_trans {s} (x : Cell B s) {m n}
    (hm : (Quotient.out x).1 ≤ m) (hn : m ≤ n) :
    inclusion B hn s (cellAt B s x m hm) =
      cellAt B s x n (le_trans hm hn) :=
  inclusion_trans B hm hn s _

/-- A source on the union can be computed in any stage containing its dimension. -/
theorem unifiedSource_in {n : ℕ} (k : Fin n) (s) (x : B.carrier (n, s)) :
    unifiedSource B k.val s (cellIn B n s x) =
      cellIn B n s ((((stageAlgebra B n).sort s).str.dim k).source x) := by
  let z := cellIn B n s x
  let m := max (k.val + 1) (Quotient.out z).1
  let p := max m n
  have hm : m ≤ p := le_max_left _ _
  have hn : n ≤ p := le_max_right _ _
  have hk : k.val < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  change cellIn B m s ((((stageAlgebra B m).sort s).str.dim ⟨k.val, hk⟩).source
    (cellAt B s z m (le_max_right _ _))) = _
  calc
    _ = cellIn B p s (inclusion B hm s
        ((((stageAlgebra B m).sort s).str.dim ⟨k.val, hk⟩).source
          (cellAt B s z m (le_max_right _ _)))) := cellIn_raise B hm s _
    _ = cellIn B p s (inclusion B hn s
        ((((stageAlgebra B n).sort s).str.dim k).source x)) := by
      rw [inclusion_source, inclusion_source]
      congr 2
      exact (cellAt_trans B z (le_max_right _ _) hm).trans
        (cellAt_eq B hn s x _)
    _ = _ := (cellIn_raise B hn s _).symm

/-- A target on the union can be computed in any stage containing its dimension. -/
theorem unifiedTarget_in {n : ℕ} (k : Fin n) (s) (x : B.carrier (n, s)) :
    unifiedTarget B k.val s (cellIn B n s x) =
      cellIn B n s ((((stageAlgebra B n).sort s).str.dim k).target x) := by
  let z := cellIn B n s x
  let m := max (k.val + 1) (Quotient.out z).1
  let p := max m n
  have hm : m ≤ p := le_max_left _ _
  have hn : n ≤ p := le_max_right _ _
  have hk : k.val < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  change cellIn B m s ((((stageAlgebra B m).sort s).str.dim ⟨k.val, hk⟩).target
    (cellAt B s z m (le_max_right _ _))) = _
  calc
    _ = cellIn B p s (inclusion B hm s
        ((((stageAlgebra B m).sort s).str.dim ⟨k.val, hk⟩).target
          (cellAt B s z m (le_max_right _ _)))) := cellIn_raise B hm s _
    _ = cellIn B p s (inclusion B hn s
        ((((stageAlgebra B n).sort s).str.dim k).target x)) := by
      rw [inclusion_target, inclusion_target]
      congr 2
      exact (cellAt_trans B z (le_max_right _ _) hm).trans
        (cellAt_eq B hn s x _)
    _ = _ := (cellIn_raise B hn s _).symm
/-- Computing a partial composition and inserting its value commutes with moving to a later stage. -/
theorem unifiedComp_move {m n : ℕ} (h : m ≤ n) (s) (k : Fin m) (x y) :
    Part.map (cellIn B m s) ((((stageAlgebra B m).sort s).str.dim k).comp x y) =
      Part.map (cellIn B n s)
        ((((stageAlgebra B n).sort s).str.dim (dimensionInclusion h k)).comp
          (inclusion B h s x) (inclusion B h s y)) := by
  rw [← inclusion_comp_map, Part.map_map]
  exact congrArg (fun f => Part.map f _) (cellIn_comp B h s).symm

/-- Partial composition on the union is computed in any sufficiently large common stage. -/
theorem unifiedComp_in {n : ℕ} (k : Fin n) (s) (x y : B.carrier (n, s)) :
    unifiedComp B k.val s (cellIn B n s x) (cellIn B n s y) =
      Part.map (cellIn B n s) ((((stageAlgebra B n).sort s).str.dim k).comp x y) := by
  let z := cellIn B n s x
  let t := cellIn B n s y
  let m := max (k.val + 1) (max (Quotient.out z).1 (Quotient.out t).1)
  let p := max m n
  have hm : m ≤ p := le_max_left _ _
  have hn : n ≤ p := le_max_right _ _
  have hk : k.val < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hx : (Quotient.out z).1 ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hy : (Quotient.out t).1 ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  change Part.map (cellIn B m s)
    ((((stageAlgebra B m).sort s).str.dim ⟨k.val, hk⟩).comp
      (cellAt B s z m hx) (cellAt B s t m hy)) = _
  calc
    _ = Part.map (cellIn B p s)
        ((((stageAlgebra B p).sort s).str.dim (dimensionInclusion hm ⟨k.val, hk⟩)).comp
          (inclusion B hm s (cellAt B s z m hx))
          (inclusion B hm s (cellAt B s t m hy))) :=
      unifiedComp_move B hm s ⟨k.val, hk⟩ _ _
    _ = Part.map (cellIn B p s)
        ((((stageAlgebra B p).sort s).str.dim (dimensionInclusion hn k)).comp
          (inclusion B hn s x) (inclusion B hn s y)) := by
      rw [cellAt_trans, cellAt_trans,
        cellAt_eq B hn s x, cellAt_eq B hn s y]
      rfl
    _ = _ := (unifiedComp_move B hn s k x y).symm

/-- All values of partial composition can be checked in a common finite stage. -/
theorem unifiedComp_mem {n : ℕ} (k : Fin n) (s) (x y z : B.carrier (n, s)) :
    cellIn B n s z ∈
      unifiedComp B k.val s (cellIn B n s x) (cellIn B n s y) ↔
        z ∈ (((stageAlgebra B n).sort s).str.dim k).comp x y := by
  rw [unifiedComp_in, Part.mem_map_iff]
  exact ⟨fun ⟨q, hq, he⟩ => (cellIn_injective B n s he) ▸ hq,
    fun hz => ⟨z, hz, rfl⟩⟩

/-- Original operations on the union are computed at every common finite stage. -/
theorem unifiedBase_in {n : ℕ} {a s} (σ : sig a s)
    (x : Word.Family ((stageAlgebra B n).carrier) a) :
    unifiedBase B σ (fun j => cellIn B n _ (x j)) =
      cellIn B n s (((stageAlgebra B n).op σ).toFun x) := by
  let z : Word.Family (Cell B) a := fun j => cellIn B n _ (x j)
  let m := wordStage B z
  let p := max m n
  have hm : m ≤ p := le_max_left _ _
  have hn : n ≤ p := le_max_right _ _
  change cellIn B m s (((stageAlgebra B m).op σ).toFun
    (fun j => cellAt B _ (z j) m (wordStage_le B z j))) = _
  calc
    _ = cellIn B p s (inclusion B hm s
        (((stageAlgebra B m).op σ).toFun
          (fun j => cellAt B _ (z j) m (wordStage_le B z j)))) :=
      cellIn_raise B hm s _
    _ = cellIn B p s (inclusion B hn s
        (((stageAlgebra B n).op σ).toFun x)) := by
      rw [inclusion_op, inclusion_op]
      congr 2
      funext j
      exact (cellAt_trans B (z j) (wordStage_le B z j) hm).trans
        (cellAt_eq B hn _ (x j) _)
    _ = _ := (cellIn_raise B hn s _).symm

end CategorialAlgebras.Omega
