import CategorialAlgebras.Dimensions.OmegaComposition
import CategorialAlgebras.Dimensions.Descriptions

/-!
# Operations and elements of the natural-dimensional functors

Realizations identify the selected elements and every defined operation value,
including the domains of partial composition. Discarded homogeneous compositions
are defined precisely on the diagonal, despite their interpreting projection term.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S : Type u} (sig : Signature.{u, v} S) (n : ℕ)

/-- Every homogeneous discretized operation agrees with the explicit discrete extension. -/
theorem omegaDiscretization_op_mem (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : Homogeneous.Symbol ℕ sig a s) (x : Word.Family B.carrier a) (q : B.carrier s) :
    omegaDiscretizationCell sig n B.toPartialAlgebra s q ∈
      ((homogeneousOmegaDiscretization sig n).transformed B.toPartialAlgebra).op σ
        (fun j => omegaDiscretizationCell sig n B.toPartialAlgebra _ (x j)) ↔
      q ∈ (omegaDiscretizedAlgebra B).toPartialAlgebra.op σ x :=
  iso_hom_mem_iff (homogeneousOmegaDiscretizationRealization sig n B) σ x q

/-- Every homogeneous truncated operation agrees with its restriction to cutoff cells. -/
theorem omegaTruncation_op_mem (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    {a s} (σ : Homogeneous.Symbol (Fin n) sig a s)
    (x : Word.Family (omegaTruncatedAlgebra B n).carrier a)
    (q : (omegaTruncatedAlgebra B n).carrier s) :
    omegaTruncationCell sig n B s q ∈
      ((homogeneousOmegaTruncation sig n).transformed B.toPartialAlgebra).op σ
        (fun j => omegaTruncationCell sig n B _ (x j)) ↔
      q ∈ (omegaTruncatedAlgebra B n).toPartialAlgebra.op σ x :=
  iso_hom_mem_iff (homogeneousOmegaTruncationRealization sig n B) σ x q

/-- Higher homogeneous compositions in an infinite discretization have exactly diagonal values. -/
theorem omegaDiscretization_comp_diagonal
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) (k : ℕ) (hk : n ≤ k)
    (s : S) (x y z : B.carrier s) :
    omegaDiscretizationCell sig n B.toPartialAlgebra s z ∈
      ((homogeneousOmegaDiscretization sig n).transformed B.toPartialAlgebra).op (.comp k s)
        (Homogeneous.pair (omegaDiscretizationCell sig n B.toPartialAlgebra s x)
          (omegaDiscretizationCell sig n B.toPartialAlgebra s y)) ↔ x = y ∧ x = z := by
  have hp : Homogeneous.pair (omegaDiscretizationCell sig n B.toPartialAlgebra s x)
      (omegaDiscretizationCell sig n B.toPartialAlgebra s y) =
      (fun j => omegaDiscretizationCell sig n B.toPartialAlgebra _ (Homogeneous.pair x y j)) := by
    funext j
    fin_cases j <;> rfl
  erw [hp, omegaDiscretization_op_mem sig n B]
  change z ∈ (if hh : k < n then _ else Homogeneous.CategoryStructure.discrete _).comp x y ↔ _
  rw [dite_eq_right (not_lt_of_ge hk)]
  exact ⟨fun ⟨he, hz⟩ => ⟨he, hz⟩, fun ⟨he, hz⟩ => ⟨he, hz⟩⟩

/-- The natural-dimensional truncation realization retains the original element. -/
@[simp] theorem homogeneousOmegaTruncationRealization_hom_val
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (s)
    (x : (omegaTruncatedAlgebra B n).carrier s) :
    ((homogeneousOmegaTruncationRealization sig n B).hom.toMap s x).val = x.val := rfl

/-- The inverse natural-dimensional truncation realization also retains the element. -/
@[simp] theorem homogeneousOmegaTruncationRealization_inv_val
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (s)
    (x : (homogeneousOmegaTruncation sig n).Cell B.toPartialAlgebra s) :
    ((homogeneousOmegaTruncationRealization sig n B).inv.toMap s x).val = x.val := by
  let e := homogeneousOmegaTruncationRealization sig n B
  exact congrArg (fun f : (homogeneousOmegaTruncation sig n).transformed B.toPartialAlgebra ⟶
    (homogeneousOmegaTruncation sig n).transformed B.toPartialAlgebra =>
      (f.toMap s x).val) e.inv_hom_id

end CategorialAlgebras.Dimensions
