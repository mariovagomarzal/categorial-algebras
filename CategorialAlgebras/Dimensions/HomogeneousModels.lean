import CategorialAlgebras.Dimensions.HomogeneousStructure
import CategorialAlgebras.Presentations.Realization

/-!
# Homogeneous dimension functors on models

The explicit discretization and truncation realize the induced transformations.
The model functors are obtained by restriction and corestriction, and the functors
on categorial algebras are transported along the model isomorphisms.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S : Type u} (sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n)

/-- Insert the empty-domain subtype of a homogeneous discretization. -/
def discretizationCell (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (s : S) (x : B.carrier s) : (homogeneousDiscretization sig h).Cell B s :=
  ⟨x, homogeneousDiscretization_isCell sig h B s x⟩

/-- Inserting the empty-domain subtype is bijective. -/
theorem discretizationCell_bijective
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig)) (s : S) :
    Function.Bijective (discretizationCell sig h B s) :=
  ⟨fun _ _ he => congrArg Subtype.val he, fun x => ⟨x.val, Subtype.ext rfl⟩⟩

/-- The explicit discretized operations have the prescribed term values. -/
theorem discretized_imageValue (B : Homogeneous.NCategorialAlgebra.{u, v, w} m sig)
    {a s} (σ : Homogeneous.Symbol (Fin n) sig a s)
    (x : Word.Family B.carrier a) {q}
    (hq : q ∈ (discretizedAlgebra B n).toPartialAlgebra.op σ x) :
    q ∈ (homogeneousDiscretization sig h).imageValue B.toPartialAlgebra σ
      (fun j => discretizationCell sig h B.toPartialAlgebra _ (x j)) := by
  cases σ with
  | base σ =>
    apply (Term.mem_partialEval_app _ _ _ _).mpr
    exact ⟨x, fun _ => Part.mem_some _, hq⟩
  | source k s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra) (Word.valuation (φ := id) x)
      (if hk : k.val < m then Homogeneous.unary (.source ⟨k.val, hk⟩ s) (.var (Word.position _ 0)) else .var (Word.position _ 0))
    change q ∈ Part.some ((if hk : k.val < m then (B.sort s).str.dim ⟨k.val, hk⟩
      else Homogeneous.CategoryStructure.discrete _).source (x 0)) at hq
    by_cases hk : k.val < m
    · erw [dite_eq_left hk, Homogeneous.partialEval_unary, Term.partialEval_var,
        Part.bind_some]
      erw [dite_eq_left hk] at hq
      exact hq
    · erw [dite_eq_right hk, Term.partialEval_var]
      erw [dite_eq_right hk] at hq
      exact hq
  | target k s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra) (Word.valuation (φ := id) x)
      (if hk : k.val < m then Homogeneous.unary (.target ⟨k.val, hk⟩ s) (.var (Word.position _ 0)) else .var (Word.position _ 0))
    change q ∈ Part.some ((if hk : k.val < m then (B.sort s).str.dim ⟨k.val, hk⟩
      else Homogeneous.CategoryStructure.discrete _).target (x 0)) at hq
    by_cases hk : k.val < m
    · erw [dite_eq_left hk, Homogeneous.partialEval_unary, Term.partialEval_var,
        Part.bind_some]
      erw [dite_eq_left hk] at hq
      exact hq
    · erw [dite_eq_right hk, Term.partialEval_var]
      erw [dite_eq_right hk] at hq
      exact hq
  | comp k s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra) (Word.valuation (φ := id) x)
      (if hk : k.val < m then Homogeneous.binary ⟨k.val, hk⟩ (.var (Word.position _ 0)) (.var (Word.position _ 1)) else .var (Word.position _ 0))
    change q ∈ (if hk : k.val < m then (B.sort s).str.dim ⟨k.val, hk⟩
      else Homogeneous.CategoryStructure.discrete _).comp (x 0) (x 1) at hq
    by_cases hk : k.val < m
    · erw [dite_eq_left hk, Homogeneous.partialEval_binary, Term.partialEval_var,
        Part.bind_some, Term.partialEval_var, Part.bind_some]
      erw [dite_eq_left hk] at hq
      exact hq
    · erw [dite_eq_right hk, Term.partialEval_var]
      erw [dite_eq_right hk] at hq
      exact Part.mem_some_iff.mpr hq.2.symm

/-- The explicit discretization realizes the induced transformation by inserting only
the empty-domain subtype.

**Formally weaker** than the informal statement. Informally, the two algebras are equal; here the
carrier of a transformed algebra is a subtype of cells, so the equality becomes an isomorphism that
is the identity on elements. -/
noncomputable def homogeneousDiscretizationRealization
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} m sig) :
    (discretizedAlgebra B n).toPartialAlgebra ≅
      (homogeneousDiscretization sig h).transformed B.toPartialAlgebra :=
  realizationIso (homogeneousDiscretization sig h) B.toPartialAlgebra
    (discretizedAlgebra B n).toPartialAlgebra
    (Homogeneous.equations_isEPAlgebra (discretizedAlgebra B n).satisfiesEquations)
    (discretizationCell sig h B.toPartialAlgebra)
    (discretizationCell_bijective sig h B.toPartialAlgebra) (discretized_imageValue sig h B)

/-- The discretization realization retains each underlying element. -/
@[simp] theorem homogeneousDiscretizationRealization_hom_val
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} m sig) (s : S) (x : B.carrier s) :
    ((homogeneousDiscretizationRealization sig h B).hom.toMap s x).val = x := rfl

/-- Discretization sends homogeneous models to homogeneous models. -/
theorem homogeneousDiscretization_isModel
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (hB : (Homogeneous.specification (Fin m) sig).IsModel B) :
    (Homogeneous.specification (Fin n) sig).IsModel
      ((homogeneousDiscretization sig h).transformed B) := by
  let C := Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = B := Homogeneous.toPartialAlgebra_ofEquations B _
  rw [← hc]
  exact model_of_iso _ (homogeneousDiscretizationRealization sig h C)
    ⟨Homogeneous.equations_isEPAlgebra (discretizedAlgebra C n).satisfiesEquations,
      fun _ ⟨e, he⟩ => he ▸ (discretizedAlgebra C n).satisfiesEquations e⟩

/-- A truncated source has the original lower source as its underlying value. -/
theorem truncated_source_val (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin m) (s : S) (x : (truncatedAlgebra h B).carrier s) :
    ((((truncatedAlgebra h B).sort s).str.dim k).source x).val =
      ((B.sort s).str.dim (dimensionInclusion h k)).source x.val := by
  change ((dimensionLE (graduatedSort B s).str
    ((cellInclusion h).monotone (le_of_lt (castSucc_lt_last k)))).identity
      ((dimensionLE (graduatedSort B s).str
        ((cellInclusion h).monotone (le_of_lt (castSucc_lt_last k)))).source x)).val = _
  rw [dimensionLE_of_lt _ _ ((cellInclusion h).lt_iff_lt.mpr (castSucc_lt_last k))]
  rfl

/-- A truncated target has the original lower target as its underlying value. -/
theorem truncated_target_val (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin m) (s : S) (x : (truncatedAlgebra h B).carrier s) :
    ((((truncatedAlgebra h B).sort s).str.dim k).target x).val =
      ((B.sort s).str.dim (dimensionInclusion h k)).target x.val := by
  change ((dimensionLE (graduatedSort B s).str
    ((cellInclusion h).monotone (le_of_lt (castSucc_lt_last k)))).identity
      ((dimensionLE (graduatedSort B s).str
        ((cellInclusion h).monotone (le_of_lt (castSucc_lt_last k)))).target x)).val = _
  rw [dimensionLE_of_lt _ _ ((cellInclusion h).lt_iff_lt.mpr (castSucc_lt_last k))]
  rfl

/-- Truncation preserves both the domain and underlying values of lower compositions. -/
theorem truncated_comp_mem (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin m) (s : S) (x y z : (truncatedAlgebra h B).carrier s) :
    z ∈ (((truncatedAlgebra h B).sort s).str.dim k).comp x y ↔
      z.val ∈ ((B.sort s).str.dim (dimensionInclusion h k)).comp x.val y.val := by
  change z ∈ (dimensionLE (graduatedSort B s).str
    ((cellInclusion h).monotone (le_of_lt (castSucc_lt_last k)))).comp x y ↔ _
  rw [dimensionLE_of_lt _ _ ((cellInclusion h).lt_iff_lt.mpr (castSucc_lt_last k))]
  exact mem_graduatedComp B _ x y z

/-- The explicit truncation has the prescribed interpreting values on its exact carriers. -/
theorem truncated_imageValue (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : Homogeneous.Symbol (Fin m) sig a s)
    (x : Word.Family ((homogeneousTruncation sig h).Cell B.toPartialAlgebra) a) {q}
    (hq : q ∈ (truncatedAlgebra h B).toPartialAlgebra.op σ x) :
    q.val ∈ (homogeneousTruncation sig h).imageValue B.toPartialAlgebra σ x := by
  cases σ with
  | base σ =>
    apply (Term.mem_partialEval_app _ _ _ _).mpr
    exact ⟨fun j => (x j).val, fun _ => Part.mem_some _,
      Part.mem_some_iff.mpr (congrArg Subtype.val (Part.mem_some_iff.mp hq))⟩
  | source k s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.unary _ _)
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    apply Part.mem_some_iff.mpr
    exact (congrArg Subtype.val (Part.mem_some_iff.mp hq)).trans
      (truncated_source_val sig h B k s (x 0))
  | target k s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.unary _ _)
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    apply Part.mem_some_iff.mpr
    exact (congrArg Subtype.val (Part.mem_some_iff.mp hq)).trans
      (truncated_target_val sig h B k s (x 0))
  | comp k s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.binary _ _ _)
    erw [Homogeneous.partialEval_binary, Term.partialEval_var, Part.bind_some,
      Term.partialEval_var, Part.bind_some]
    exact (truncated_comp_mem sig h B k s _ _ _).mp hq

/-- The induced truncation equals the explicit algebra on the exact selected subtypes. -/
theorem homogeneousTruncation_transformed (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    (homogeneousTruncation sig h).transformed B.toPartialAlgebra =
      (truncatedAlgebra h B).toPartialAlgebra :=
  transformed_eq_of_realization _ _ _
    (Homogeneous.equations_isEPAlgebra (truncatedAlgebra h B).satisfiesEquations)
    (truncated_imageValue sig h B)

/-- Truncation sends homogeneous models to homogeneous models. -/
theorem homogeneousTruncation_isModel
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    (Homogeneous.specification (Fin m) sig).IsModel
      ((homogeneousTruncation sig h).transformed B) := by
  let C := Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = B := Homogeneous.toPartialAlgebra_ofEquations B _
  rw [← hc, homogeneousTruncation_transformed sig h C]
  exact ⟨Homogeneous.equations_isEPAlgebra (truncatedAlgebra h C).satisfiesEquations,
    fun _ ⟨e, he⟩ => he ▸ (truncatedAlgebra h C).satisfiesEquations e⟩

end CategorialAlgebras.Dimensions
