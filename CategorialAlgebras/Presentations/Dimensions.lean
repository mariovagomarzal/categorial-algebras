import CategorialAlgebras.Homogeneous.Identification
import CategorialAlgebras.Heterogeneous.Identification
import CategorialAlgebras.HepDerivor.Comparison

/-!
# Finite dimensions and cells

The top dimension is `Fin.last n`; every smaller dimension belongs to `Fin n`.
Cells in the top dimension are unrestricted. Lower cells are fixed by source.
-/

universe u v w

namespace CategorialAlgebras.Presentations

/-- The lower endpoint of a strictly increasing pair is a composition dimension. -/
def lowerDimension {n : ℕ} {j k : Fin (n + 1)} (h : j < k) : Fin n :=
  ⟨j.val, lt_of_lt_of_le h (Nat.le_of_lt_succ k.isLt)⟩

/-- Reinserting the lower endpoint does not change its value. -/
@[simp] theorem lowerDimension_castSucc {n : ℕ} {j k : Fin (n + 1)} (h : j < k) :
    (lowerDimension h).castSucc = j := rfl

/-- Every composition dimension is strictly below the top dimension. -/
theorem castSucc_lt_last {n : ℕ} (k : Fin n) : k.castSucc < Fin.last n := k.isLt

/-- The lower endpoint of the pair from a composition dimension to the top is itself. -/
@[simp] theorem lowerDimension_last {n : ℕ} (k : Fin n) :
    lowerDimension (castSucc_lt_last k) = k := rfl

/-- A finite-dimensional cell, including all elements at the top dimension. -/
def IsFiniteCell {n : ℕ} {A : Type w} (C : Homogeneous.Structure (Fin n) A)
    (k : Fin (n + 1)) (x : A) : Prop :=
  ∀ h : k.val < n, C.IsCell ⟨k.val, h⟩ x

/-- At the top dimension every element is a cell. -/
@[simp] theorem isFiniteCell_last {n : ℕ} {A : Type w}
    (C : Homogeneous.Structure (Fin n) A) (x : A) : IsFiniteCell C (Fin.last n) x :=
  fun h => (Nat.lt_irrefl n h).elim

/-- At a lower dimension the condition is the usual fixed-source condition. -/
@[simp] theorem isFiniteCell_castSucc {n : ℕ} {A : Type w}
    (C : Homogeneous.Structure (Fin n) A) (k : Fin n) (x : A) :
    IsFiniteCell C k.castSucc x ↔ C.IsCell k x :=
  ⟨fun h => h k.isLt, fun h _ => h⟩

/-- Finite cells remain cells in every larger dimension. -/
theorem isFiniteCell_mono {n : ℕ} {A : Type w}
    (C : Homogeneous.Structure (Fin n) A) {j k : Fin (n + 1)} (h : j ≤ k)
    {x : A} (hx : IsFiniteCell C j x) : IsFiniteCell C k x := by
  intro hk
  exact C.isCell_mono (show (⟨j.val, lt_of_le_of_lt h hk⟩ : Fin n) ≤ ⟨k.val, hk⟩ from h)
    (hx _)

/-- Sources are cells in their own dimension. -/
theorem source_isCell {n : ℕ} {A : Type w}
    (C : Homogeneous.Structure (Fin n) A) (k : Fin n) (x : A) :
    C.IsCell k ((C.dim k).source x) := (C.dim k).source_source x

/-- Targets are cells in their own dimension. -/
theorem target_isCell {n : ℕ} {A : Type w}
    (C : Homogeneous.Structure (Fin n) A) (k : Fin n) (x : A) :
    C.IsCell k ((C.dim k).target x) := (C.dim k).source_target x

/-- A lower composition of higher cells is again a higher cell. -/
theorem comp_isCell {n : ℕ} {A : Type w}
    (C : Homogeneous.Structure (Fin n) A) {j k : Fin n} (h : j < k)
    {x y z : A} (hx : C.IsCell k x) (hy : C.IsCell k y)
    (hz : z ∈ (C.dim j).comp x y) : C.IsCell k z := by
  have hv := (C.compatible j k h).source_comp x y z hz
  rw [hx, hy] at hv
  exact Part.mem_unique hv hz

/-- Original operations preserve the dimension of cells, including nullary operations. -/
theorem operation_isCell {n : ℕ} {S : Type u} {sig : Signature.{u, v} S}
    (A : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) {a s} (σ : sig a s)
    (k : Fin n) (x : Word.Family A.carrier a)
    (hx : ∀ j, (A.sort _).str.IsCell k (x j)) :
    (A.sort s).str.IsCell k ((A.op σ).toFun x) := by
  exact ((A.op σ).map_source k x).symm.trans
    (congrArg (A.op σ).toFun (funext hx))

/-- Identities between distinct dimensions are injective. -/
theorem identity_injective {I : Type*} [Preorder I] {A : I → Type w}
    (C : Heterogeneous.Structure I A) {j k} (h : j < k) :
    Function.Injective (C.dim j k h).identity :=
  Function.LeftInverse.injective (C.dim j k h).source_identity

end CategorialAlgebras.Presentations
