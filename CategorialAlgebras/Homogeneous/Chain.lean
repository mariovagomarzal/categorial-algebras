import CategorialAlgebras.Homogeneous.Identification
import Mathlib.Order.Fin.Basic
import Mathlib.Order.ULift

/-!
# Chain examples of homogeneous higher categories

On a linear order, a boundary is $x\mapsto\min(x,a)$ and a compatible pair composes
by maximum. Increasing cutoffs give compatible category structures. Finite chains
provide cells of arbitrarily high finite dimension.
-/

universe u v w

namespace CategorialAlgebras
namespace Homogeneous

variable {L : Type u} [LinearOrder L]

/-- The category on a chain with boundary cutoff $a$ and composition given by maximum. -/
abbrev chainDimension (a : L) : CategoryStructure L where
  source x := min x a
  target x := min x a
  comp x y := ⟨min x a = min y a, fun _ => max x y⟩
  source_source x := min_eq_left (min_le_right x a)
  source_target x := min_eq_left (min_le_right x a)
  target_source x := min_eq_left (min_le_right x a)
  target_target x := min_eq_left (min_le_right x a)
  comp_dom _ _ := Iff.rfl
  source_comp x y z h := by
    rcases h with ⟨h, rfl⟩
    rw [min_max_distrib_right, h, max_self]
  target_comp x y z h := by
    rcases h with ⟨h, rfl⟩
    rw [min_max_distrib_right, h, max_self]
  comp_source x := ⟨(min_eq_left (min_le_right x a)).symm, max_eq_left (min_le_left x a)⟩
  target_comp_self x := ⟨min_eq_left (min_le_right x a), max_eq_right (min_le_left x a)⟩
  assoc x y z xy yz hxy hyz := by
    rcases hxy with ⟨hxy, rfl⟩
    rcases hyz with ⟨hyz, rfl⟩
    refine ⟨max (max x y) z, ⟨?_, rfl⟩, ⟨?_, ?_⟩⟩
    · change min (max x y) a = min z a
      rw [min_max_distrib_right, hxy, max_self, hyz]
    · change min x a = min (max y z) a
      rw [min_max_distrib_right, ← hyz, max_self, hxy]
    · exact (max_assoc x y z).symm

/-- Increasing cutoffs on a chain give compatible category structures. -/
theorem chain_compatible {a b : L} (hab : a ≤ b) :
    Compatible (chainDimension a) (chainDimension b) where
  source_source x := min_eq_left ((min_le_right x a).trans hab)
  target_target x := min_eq_left ((min_le_right x a).trans hab)
  source_source_low x := by change min (min x b) a = min x a; rw [min_assoc, min_eq_right hab]
  target_target_low x := by change min (min x b) a = min x a; rw [min_assoc, min_eq_right hab]
  source_target x := by change min (min x b) a = min x a; rw [min_assoc, min_eq_right hab]
  target_source x := by change min (min x b) a = min x a; rw [min_assoc, min_eq_right hab]
  source_comp x y z h := by
    rcases h with ⟨h, rfl⟩
    refine ⟨?_, ?_⟩
    · change min (min x b) a = min (min y b) a
      simpa only [min_assoc, min_eq_right hab] using h
    · exact (min_max_distrib_right x y b).symm
  target_comp x y z h := by
    rcases h with ⟨h, rfl⟩
    refine ⟨?_, ?_⟩
    · change min (min x b) a = min (min y b) a
      simpa only [min_assoc, min_eq_right hab] using h
    · exact (min_max_distrib_right x y b).symm
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    rcases hxy with ⟨hxy, rfl⟩
    rcases hzt with ⟨hzt, rfl⟩
    rcases hxz with ⟨hxz, rfl⟩
    rcases hyt with ⟨hyt, rfl⟩
    refine ⟨max (max x y) (max z t), ⟨?_, rfl⟩, ⟨?_, ?_⟩⟩
    · change min (max x y) b = min (max z t) b
      rw [min_max_distrib_right, min_max_distrib_right, hxz, hyt]
    · change min (max x z) a = min (max y t) a
      rw [min_max_distrib_right, min_max_distrib_right, hxy, hzt]
    · exact max_max_max_comm x z y t

/-- The boundary cutoff at dimension $j$ in the chain with $k+2$ elements. -/
def chainCutoff (k j : ℕ) : Fin (k + 2) :=
  ⟨min j (k + 1), (min_le_right j (k + 1)).trans_lt (Nat.lt_succ_self _)⟩

/-- Chain cutoffs increase with the dimension. -/
theorem chainCutoff_mono (k : ℕ) : Monotone (chainCutoff k) :=
  fun _ _ h => min_le_min_right _ h

/-- A bounded homogeneous category with cells $0,\ldots,k+1$. -/
abbrev boundedChain (k : ℕ) : HigherCategory.{0, w} ℕ where
  carrier := ULift.{w} (Fin (k + 2))
  str.dim j := chainDimension (ULift.up (chainCutoff k j))
  str.compatible _ _ h := chain_compatible (show (ULift.up (chainCutoff k _) : ULift.{w} _) ≤
    ULift.up (chainCutoff k _) from chainCutoff_mono k h.le)

/-- Every cell of the bounded chain is a $(k+1)$-cell. -/
theorem boundedChain_top (k : ℕ) (x : (boundedChain.{w} k).carrier) :
    (boundedChain.{w} k).str.IsCell (k + 1) x := by
  change min x (ULift.up (chainCutoff k (k + 1))) = x
  apply min_eq_left
  change x.down.val ≤ min (k + 1) (k + 1)
  simpa only [min_self] using Nat.le_of_lt_succ x.down.isLt

/-- The top cell in a bounded chain. -/
def chainTop (k : ℕ) : (boundedChain.{w} k).carrier := ULift.up ⟨k + 1, Nat.lt_succ_self _⟩

/-- The top cell is not a $k$-cell. -/
theorem boundedChain_not_cell (k : ℕ) : ¬ (boundedChain.{w} k).str.IsCell k (chainTop k) := by
  intro h
  have hv := congrArg (fun x => x.down.val) h
  change min (k + 1) (min k (k + 1)) = k + 1 at hv
  simp only [min_eq_left (Nat.le_succ k), min_eq_right (Nat.le_succ k)] at hv
  exact Nat.ne_of_lt (Nat.lt_succ_self k) hv

/-- The least cell is fixed by every boundary of every dimension. -/
theorem boundedChain_zero (k j : ℕ) :
    ((boundedChain.{w} k).str.dim j ).source (ULift.up 0) = ULift.up 0 := min_eq_left (Fin.zero_le _)

/-- A constant higher functor picking the least cell in a bounded chain. -/
def chainConstant (k : ℕ) (C : HigherCategory.{0, w} ℕ) : Functor C (boundedChain.{w} k) where
  toFun _ := ULift.up 0
  map_source j _ := (boundedChain_zero k j).symm
  map_target j _ := (boundedChain_zero k j).symm
  map_comp _ _ _ _ _ := ⟨rfl, max_self (ULift.up 0)⟩

/-- Interpret every sort by a bounded chain and every original operation by its least cell. -/
def chainAlgebra {S : Type u} (sig : Signature.{u, v} S) (k : ℕ) : CategorialAlgebra.{0, u, v, w} ℕ sig where
  sort _ := boundedChain k
  op _ := chainConstant k _

/-- The chain algebra has only finite-dimensional cells. -/
theorem chainAlgebra_finite {S : Type u} (sig : Signature.{u, v} S) (k : ℕ) :
    (chainAlgebra.{u, v, w} sig k).FiniteDimensional := fun _ x => ⟨k + 1, boundedChain_top k x⟩

end Homogeneous
end CategorialAlgebras
