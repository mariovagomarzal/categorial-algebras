import CategorialAlgebras.Dimensions.Functors

/-!
# Operations of the dimension transformations

The realization isomorphisms give exact membership formulas for all operations.
In the added dimensions, the interpreting composition term is a total projection,
whereas the transformed composition has precisely the diagonal as its domain.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

/-- An isomorphism of partial algebras preserves and reflects every operation value. -/
theorem iso_hom_mem_iff {S : Type u} {sig : Signature.{u, v} S}
    {A B : PartialAlgebra.{u, v, w} sig} (e : A ≅ B) {a s} (σ : sig a s)
    (x : Word.Family A.carrier a) (q : A.carrier s) :
    e.hom.toMap s q ∈ B.op σ (fun j => e.hom.toMap _ (x j)) ↔ q ∈ A.op σ x := by
  have he t (z : A.carrier t) : e.inv.toMap t (e.hom.toMap t z) = z :=
    congrArg (fun f : A ⟶ A => f.toMap t z) e.hom_inv_id
  constructor
  · intro hq
    have hh := e.inv.map_op σ _ hq
    simpa only [he] using hh
  · exact e.hom.map_op σ x

variable {S : Type u} (sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n)

/-- All homogeneous discretized operation values are those of the explicit structure. -/
theorem discretization_op_mem (B : Homogeneous.NCategorialAlgebra.{u, v, w} m sig)
    {a s} (σ : Homogeneous.Symbol (Fin n) sig a s)
    (x : Word.Family B.carrier a) (q : B.carrier s) :
    discretizationCell sig h B.toPartialAlgebra s q ∈
        ((homogeneousDiscretization sig h).transformed B.toPartialAlgebra).op σ
          (fun j => discretizationCell sig h B.toPartialAlgebra _ (x j)) ↔
      q ∈ (discretizedAlgebra B n).toPartialAlgebra.op σ x :=
  iso_hom_mem_iff (homogeneousDiscretizationRealization sig h B) σ x q

/-- All homogeneous truncated operation values are the restrictions of the explicit structure. -/
theorem truncation_op_mem (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : Homogeneous.Symbol (Fin m) sig a s)
    (x : Word.Family ((homogeneousTruncation sig h).Cell B.toPartialAlgebra) a)
    (q : (homogeneousTruncation sig h).Cell B.toPartialAlgebra s) :
    q ∈ ((homogeneousTruncation sig h).transformed B.toPartialAlgebra).op σ x ↔
      q ∈ (truncatedAlgebra h B).toPartialAlgebra.op σ x := by
  have hop := op_eq_of_same_carrier (homogeneousTruncation_transformed sig h B)
  exact congrArg (fun op => q ∈ op σ x) hop |>.to_iff

/-- A higher homogeneous discretized composition has exactly its diagonal values. -/
theorem discretization_comp_diagonal (B : Homogeneous.NCategorialAlgebra.{u, v, w} m sig)
    (k : Fin n) (hk : m ≤ k.val) (s : S) (x y z : B.carrier s) :
    discretizationCell sig h B.toPartialAlgebra s z ∈
        ((homogeneousDiscretization sig h).transformed B.toPartialAlgebra).op (.comp k s)
          (Homogeneous.pair (discretizationCell sig h B.toPartialAlgebra s x)
            (discretizationCell sig h B.toPartialAlgebra s y)) ↔ x = y ∧ x = z := by
  have hp : Homogeneous.pair (discretizationCell sig h B.toPartialAlgebra s x)
      (discretizationCell sig h B.toPartialAlgebra s y) =
      (fun j => discretizationCell sig h B.toPartialAlgebra _ (Homogeneous.pair x y j)) := by
    funext j
    fin_cases j <;> rfl
  erw [hp]
  erw [discretization_op_mem sig h B (.comp k s) (Homogeneous.pair x y) z]
  change z ∈ (if hh : k.val < m then _ else Homogeneous.CategoryStructure.discrete _).comp x y ↔ _
  erw [dite_eq_right (not_lt_of_ge hk)]
  exact ⟨fun ⟨he, hz⟩ => ⟨he, hz⟩, fun ⟨he, hz⟩ => ⟨he, hz⟩⟩

/-- The term interpreting a discarded composition is total on every pair, independently
of the diagonal domain imposed by the transformed signature. -/
theorem discretization_comp_image_total
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (k : Fin n) (hk : m ≤ k.val) (s : S)
    (x : Word.Family ((homogeneousDiscretization sig h).Cell B) [s, s]) :
    ((homogeneousDiscretization sig h).imageValue B (.comp k s) x).Dom := by
  change (Term.partialEval (A := B) _ (if hh : k.val < m then _ else _)).Dom
  erw [dite_eq_right (not_lt_of_ge hk), Term.partialEval_var]
  exact Part.some_dom _

/-- Membership in every heterogeneous transformed operation is exactly membership in
its reindexed operation, including the discrete operations on collapsed pairs. -/
theorem heterogeneousDimension_op_mem {I J : Type} [LinearOrder I] [LinearOrder J]
    (f : I →o J) (hf : Saturating f) (B : Heterogeneous.CategorialAlgebra.{0, u, v, w} J sig)
    {a s} (σ : Heterogeneous.Symbol I sig a s)
    (x : Word.Family (reindexedAlgebra B f hf).carrier a)
    (q : (reindexedAlgebra B f hf).carrier s) :
    heterogeneousDimensionCell sig f B.toPartialAlgebra s q ∈
        ((heterogeneousDimension sig f).transformed B.toPartialAlgebra).op σ
          (fun j => heterogeneousDimensionCell sig f B.toPartialAlgebra _ (x j)) ↔
      q ∈ (reindexedAlgebra B f hf).toPartialAlgebra.op σ x :=
  iso_hom_mem_iff (heterogeneousDimensionRealization sig f hf B) σ x q

end CategorialAlgebras.Dimensions
