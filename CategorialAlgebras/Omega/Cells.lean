import CategorialAlgebras.Dimensions.HeterogeneousCounitStructure
import Mathlib.Order.DirectedInverseSystem

/-!
# Cells identified along dimensional identities

The quotient of the disjoint union of dimensional carriers identifies cells
with their identities. Equality can be checked in every common higher dimension.
The quotient has the inductive universal property in sets, including empty carriers.
-/

universe u v w x

namespace CategorialAlgebras.Omega

open Dimensions

variable {S : Type u} {sig : Signature.{u, v} S}
variable (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)

/-- Raise a cell by the identity between weakly increasing dimensions. -/
noncomputable def inclusion {j k : ℕ} (h : j ≤ k) (s : S) :
    B.carrier (j, s) → B.carrier (k, s) :=
  (dimensionLE (B.sort s).str h).identity

/-- Raising within a single dimension is the identity. -/
@[simp] theorem inclusion_self (k : ℕ) (s : S) (x : B.carrier (k, s)) :
    inclusion B (le_refl k) s x = x := by
  simp only [inclusion, dimensionLE_self]
  rfl

/-- Successive identity inclusions compose to the direct inclusion. -/
@[simp] theorem inclusion_trans {i j k : ℕ} (h : i ≤ j) (q : j ≤ k)
    (s : S) (x : B.carrier (i, s)) :
    inclusion B q s (inclusion B h s x) = inclusion B (le_trans h q) s x :=
  dimensionLE_identity_trans (B.sort s).str h q x

/-- Every dimensional identity inclusion is injective. -/
theorem inclusion_injective {j k : ℕ} (h : j ≤ k) (s : S) :
    Function.Injective (inclusion B h s) :=
  Function.LeftInverse.injective (dimensionLE (B.sort s).str h).source_identity

/-- The dimensional identity inclusions form a directed system. -/
instance inclusionDirected (s : S) : DirectedSystem
    (fun k => B.carrier (k, s)) (fun {_ _} h => inclusion B h s) where
  map_self {i} x := inclusion_self B i s x
  map_map {_ _ _} h q x := inclusion_trans B h q s x

/-- The injective map between two dimensional carriers. -/
noncomputable def inclusionEmbedding {j k : ℕ} (h : j ≤ k) (s : S) :
    B.carrier (j, s) ↪ B.carrier (k, s) :=
  ⟨inclusion B h s, inclusion_injective B h s⟩

/-- The bundled inclusions form the same directed system. -/
instance embeddingDirected (s : S) : DirectedSystem
    (fun k => B.carrier (k, s)) (fun {_ _} h => inclusionEmbedding B h s) :=
  inclusionDirected B s

/-- Representatives are equivalent when they agree in a common higher dimension. -/
noncomputable def cellSetoid (s : S) : Setoid (Σ k, B.carrier (k, s)) :=
  DirectLimit.setoid (fun _ _ h => inclusionEmbedding B h s)

/-- The cells obtained by identifying every cell with its dimensional identities. -/
def Cell (s : S) : Type w := Quotient (cellSetoid B s)

/-- Insert a dimensional cell into the quotient. -/
noncomputable def cellIn (k : ℕ) (s : S) (x : B.carrier (k, s)) : Cell B s :=
  Quotient.mk _ ⟨k, x⟩

/-- Equality of classes is equality in some common higher dimension. -/
theorem cellIn_eq_iff (j k : ℕ) (s : S) (x : B.carrier (j, s)) (y : B.carrier (k, s)) :
    cellIn B j s x = cellIn B k s y ↔
      ∃ (p : ℕ) (hj : j ≤ p) (hk : k ≤ p), inclusion B hj s x = inclusion B hk s y :=
  Quotient.eq

/-- Inserting an identity gives the original class. -/
@[simp] theorem cellIn_inclusion {j k : ℕ} (h : j ≤ k) (s : S) (x : B.carrier (j, s)) :
    cellIn B k s (inclusion B h s x) = cellIn B j s x := by
  apply Quotient.sound
  exact ⟨k, le_refl _, h, inclusion_self B k s (inclusion B h s x)⟩

/-- Every dimensional carrier embeds in the quotient. -/
theorem cellIn_injective (k : ℕ) (s : S) : Function.Injective (cellIn B k s) := by
  intro x y h
  obtain ⟨p, hp, _, he⟩ := (cellIn_eq_iff B k k s x y).mp h
  exact inclusion_injective B hp s he

/-- Equal classes agree in any common higher dimension. -/
theorem cellIn_eq_at {j k p : ℕ} (hj : j ≤ p) (hk : k ≤ p) (s : S)
    (x : B.carrier (j, s)) (y : B.carrier (k, s))
    (h : cellIn B j s x = cellIn B k s y) : inclusion B hj s x = inclusion B hk s y := by
  obtain ⟨q, hq, hq', he⟩ := (cellIn_eq_iff B j k s x y).mp h
  apply inclusion_injective B (le_max_left p q) s
  simpa only [inclusion_trans] using congrArg (inclusion B (le_max_right p q) s) he

/-- The equivalence relation is precisely identification along identities in either direction. -/
theorem cellIn_eq_iff_comparable (j k : ℕ) (s : S)
    (x : B.carrier (j, s)) (y : B.carrier (k, s)) :
    cellIn B j s x = cellIn B k s y ↔
      (∃ h : j ≤ k, inclusion B h s x = y) ∨
        (∃ h : k ≤ j, x = inclusion B h s y) := by
  constructor
  · intro h
    rcases le_total j k with hj | hk
    · exact Or.inl ⟨hj, by simpa using cellIn_eq_at B hj (le_refl k) s x y h⟩
    · exact Or.inr ⟨hk, by simpa using cellIn_eq_at B (le_refl j) hk s x y h⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩) <;> simp

/-- Every quotient cell has a representative in some dimension. -/
theorem cellIn_surjective (s : S) (x : Cell B s) : ∃ k y, cellIn B k s y = x := by
  obtain ⟨⟨k, y⟩, rfl⟩ := Quotient.mk_surjective x
  exact ⟨k, y, rfl⟩

/-- A selected representative of a quotient cell. -/
noncomputable def representative {s : S} (x : Cell B s) : Σ k, B.carrier (k, s) :=
  Quotient.out x

/-- Insertion of the selected representative recovers the cell. -/
theorem representative_in {s : S} (x : Cell B s) :
    cellIn B (representative B x).1 s (representative B x).2 = x :=
  Quotient.out_eq x

/-- A finite family of cells has common representatives above every prescribed bound. -/
theorem cell_cover {ι : Type*} [Fintype ι] (sorts : ι → S)
    (x : ∀ i, Cell B (sorts i)) (bound : ℕ) :
    ∃ p, bound ≤ p ∧ ∃ y : ∀ i, B.carrier (p, sorts i),
      ∀ i, cellIn B p (sorts i) (y i) = x i := by
  classical
  let p := max bound (Finset.univ.sup (fun i => (representative B (x i)).1))
  have hp i : (representative B (x i)).1 ≤ p :=
    le_trans (Finset.le_sup (f := fun i => (representative B (x i)).1)
      (Finset.mem_univ i)) (le_max_right _ _)
  refine ⟨p, le_max_left _ _, (fun i => inclusion B (hp i) _ (representative B (x i)).2), ?_⟩
  intro i
  exact (cellIn_inclusion B (hp i) _ _).trans (representative_in B (x i))

/-- Descend a compatible family of set maps to the quotient. -/
noncomputable def cellDesc {s : S} {L : Type x} (f : ∀ k, B.carrier (k, s) → L)
    (hf : ∀ {j k} (h : j ≤ k) x, f k (inclusion B h s x) = f j x) : Cell B s → L :=
  Quotient.lift (fun x => f x.1 x.2) (by
    rintro ⟨j, x⟩ ⟨k, y⟩ ⟨p, hj, hk, he⟩
    exact (hf hj x).symm.trans ((congrArg (f p) he).trans (hf hk y)))

/-- The descended set map has the specified value on every representative. -/
@[simp] theorem cellDesc_in {s : S} {L : Type x} (f : ∀ k, B.carrier (k, s) → L)
    (hf : ∀ {j k} (h : j ≤ k) x, f k (inclusion B h s x) = f j x) (k) (x) :
    cellDesc B f hf (cellIn B k s x) = f k x := rfl

/-- The quotient and its dimensional injections have the inductive universal property in sets. -/
theorem cell_inductive_limit {s : S} {L : Type x} (f : ∀ k, B.carrier (k, s) → L)
    (hf : ∀ {j k} (h : j ≤ k) x, f k (inclusion B h s x) = f j x) :
    ∃! g : Cell B s → L, ∀ k x, g (cellIn B k s x) = f k x := by
  refine ⟨cellDesc B f hf, fun _ _ => rfl, ?_⟩
  intro g hg
  funext x
  obtain ⟨k, y, rfl⟩ := cellIn_surjective B s x
  exact hg k y

end CategorialAlgebras.Omega
