import CategorialAlgebras.Omega.UnifiedStructure

/-!
# Representatives and finite-dimensional cells in unification

Boundaries are represented in their own dimension. Composition and the
original operations are calculated on representatives in a common dimension.
The $k$-cells are precisely the classes with a representative in dimension $k$.
-/

universe u v w
namespace CategorialAlgebras.Omega
open Dimensions
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)

/-- A source is the class of the original lower-dimensional source. -/
theorem unifiedSource_representative {k p : ℕ} (h : k < p) (s : S)
    (x : B.carrier (p, s)) :
    unifiedSource B k s (cellIn B p s x) =
      cellIn B k s (((B.sort s).str.dim k p h).source x) := by
  rw [unifiedSource_in B ⟨k, h⟩ s]
  simpa only [stageAlgebra, stageSort, Presentations.collapseDimension,
    inclusion, dimensionLE_of_lt _ _ h] using
      cellIn_inclusion B h.le s (((B.sort s).str.dim k p h).source x)

/-- A target is the class of the original lower-dimensional target. -/
theorem unifiedTarget_representative {k p : ℕ} (h : k < p) (s : S)
    (x : B.carrier (p, s)) :
    unifiedTarget B k s (cellIn B p s x) =
      cellIn B k s (((B.sort s).str.dim k p h).target x) := by
  rw [unifiedTarget_in B ⟨k, h⟩ s]
  simpa only [stageAlgebra, stageSort, Presentations.collapseDimension,
    inclusion, dimensionLE_of_lt _ _ h] using
      cellIn_inclusion B h.le s (((B.sort s).str.dim k p h).target x)

/-- Compositions have the original domain and the class of the original value. -/
theorem unifiedComp_representative {k p : ℕ} (h : k < p) (s : S)
    (x y : B.carrier (p, s)) :
    unifiedComp B k s (cellIn B p s x) (cellIn B p s y) =
      Part.map (cellIn B p s) (((B.sort s).str.dim k p h).comp x y) :=
  unifiedComp_in B ⟨k, h⟩ s x y

/-- The domain of composition of representatives is exactly boundary matching. -/
theorem unifiedComp_dom {k p : ℕ} (h : k < p) (s : S)
    (x y : B.carrier (p, s)) :
    (unifiedComp B k s (cellIn B p s x) (cellIn B p s y)).Dom ↔
      ((B.sort s).str.dim k p h).source x = ((B.sort s).str.dim k p h).target y := by
  rw [unifiedComp_representative B h s]
  exact ((B.sort s).str.dim k p h).comp_dom x y

/-- Original operations are computed on representatives in any common dimension. -/
theorem unifiedBase_representative {a s} (σ : sig a s) (p : ℕ)
    (x : Word.Family (fun s => B.carrier (p, s)) a) :
    unifiedBase B σ (fun j => cellIn B p _ (x j)) =
      cellIn B p s ((B.op σ).toFun p x) :=
  unifiedBase_in B σ x

/-- Every cell represented in dimension $k$ is fixed by its $k$-source. -/
theorem cellIn_isCell (k : ℕ) (s : S) (x : B.carrier (k, s)) :
    unifiedSource B k s (cellIn B k s x) = cellIn B k s x := by
  calc
    _ = unifiedSource B k s (cellIn B (k+1) s (inclusion B (Nat.le_succ k) s x)) :=
      congrArg (unifiedSource B k s) (cellIn_raise B (Nat.le_succ k) s x)
    _ = cellIn B k s (((B.sort s).str.dim k (k+1) (Nat.lt_succ_self k)).source
        (inclusion B (Nat.le_succ k) s x)) :=
      unifiedSource_representative B (Nat.lt_succ_self k) s _
    _ = cellIn B k s x := by
      apply congrArg (cellIn B k s)
      simpa only [inclusion, dimensionLE_of_lt _ _ (Nat.lt_succ_self k)] using
        ((B.sort s).str.dim k (k+1) (Nat.lt_succ_self k)).source_identity x

/-- The $k$-cells of unification are exactly classes of original $k$-cells. -/
theorem unified_isCell_iff (k : ℕ) (s : S) (x : Cell B s) :
    ((unifiedAlgebra B).sort s).str.IsCell k x ↔
      ∃ y : B.carrier (k, s), cellIn B k s y = x := by
  constructor
  · intro hx
    obtain ⟨p, hp, y, hy⟩ := cell_cover B (fun _ : Fin 1 => s) ![x] (k + 1)
    have h := unifiedSource_representative B
      (lt_of_lt_of_le (Nat.lt_succ_self k) hp) s (y 0)
    rw [hy 0] at h
    exact ⟨_, h.symm.trans hx⟩
  · rintro ⟨y, rfl⟩
    exact cellIn_isCell B k s y

/-- Unification has finite-dimensional cells, including dimension zero. -/
theorem unified_finite : (unifiedAlgebra B).FiniteDimensional := by
  intro s x
  obtain ⟨k, y, rfl⟩ := cellIn_surjective B s x
  exact ⟨k, cellIn_isCell B k s y⟩

/-- Sources above a representative's dimension fix its class. -/
theorem unifiedSource_high {p k : ℕ} (h : p ≤ k) (s : S) (x : B.carrier (p, s)) :
    unifiedSource B k s (cellIn B p s x) = cellIn B p s x :=
  ((unifiedAlgebra B).sort s).str.isCell_mono h (cellIn_isCell B p s x)

/-- Targets above a representative's dimension fix its class. -/
theorem unifiedTarget_high {p k : ℕ} (h : p ≤ k) (s : S) (x : B.carrier (p, s)) :
    unifiedTarget B k s (cellIn B p s x) = cellIn B p s x :=
  ((unifiedAlgebra B).sort s).str.isCell_iff_target k _ |>.mp (unifiedSource_high B h s x)

/-- Composition above the representatives' dimension is exactly diagonal composition. -/
theorem unifiedComp_high {p k : ℕ} (h : p ≤ k) (s : S)
    (x y z : B.carrier (p, s)) :
    cellIn B p s z ∈ unifiedComp B k s (cellIn B p s x) (cellIn B p s y) ↔
      x = y ∧ x = z := by
  constructor
  · intro hz
    have hd := (unifiedDimension B k s).comp_dom _ _ |>.mp hz.1
    change unifiedSource B k s (cellIn B p s x) = unifiedTarget B k s (cellIn B p s y) at hd
    rw [unifiedSource_high B h, unifiedTarget_high B h] at hd
    have hxy := cellIn_injective B p s hd
    subst y
    have hu := (unifiedDimension B k s).comp_source (cellIn B p s x)
    change _ ∈ unifiedComp B k s _ (unifiedSource B k s _) at hu
    rw [unifiedSource_high B h] at hu
    exact ⟨rfl, cellIn_injective B p s (Part.mem_unique hu hz)⟩
  · rintro ⟨rfl,rfl⟩
    have hu := (unifiedDimension B k s).comp_source (cellIn B p s x)
    change _ ∈ unifiedComp B k s _ (unifiedSource B k s _) at hu
    rwa [unifiedSource_high B h] at hu

end CategorialAlgebras.Omega
