import CategorialAlgebras.Dimensions.HeterogeneousStructure
import CategorialAlgebras.Presentations.Realization

/-!
# Heterogeneous dimension functors on models

Initially strict, saturating changes of dimension repeat the terminal carrier
with discrete pair structures. Their explicit operations realize the induced
transformations with empty cell domains.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {I J : Type} [LinearOrder I] [LinearOrder J]
variable {S : Type u} (sig : Signature.{u, v} S) (f : I →o J)

/-- Insert the empty-domain subtype of a heterogeneous dimension change. -/
def heterogeneousDimensionCell
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol J sig))
    (p : I × S) (x : B.carrier (dimensionSortMap f p)) :
    (heterogeneousDimension sig f).Cell B p :=
  ⟨x, heterogeneousDimension_isCell sig f B p x⟩

/-- The insertion of a heterogeneous empty-domain subtype is bijective. -/
theorem heterogeneousDimensionCell_bijective
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol J sig)) (p : I × S) :
    Function.Bijective (heterogeneousDimensionCell sig f B p) :=
  ⟨fun _ _ he => congrArg Subtype.val he, fun x => ⟨x.val, Subtype.ext rfl⟩⟩

/-- The explicit reindexed operations have the prescribed interpreting term values. -/
theorem reindexed_imageValue (hf : Saturating f)
    (B : Heterogeneous.CategorialAlgebra.{0, u, v, w} J sig)
    {a s} (σ : Heterogeneous.Symbol I sig a s)
    (x : Word.Family (reindexedAlgebra B f hf).carrier a) {q}
    (hq : q ∈ (reindexedAlgebra B f hf).toPartialAlgebra.op σ x) :
    q ∈ (heterogeneousDimension sig f).imageValue B.toPartialAlgebra σ
      (fun j => heterogeneousDimensionCell sig f B.toPartialAlgebra _ (x j)) := by
  cases σ with
  | @base k a s σ =>
    apply (Term.mem_partialEval_app _ _ _ _).mpr
    let y : Word.Family B.carrier (Heterogeneous.dimensionWord (f k) a) := fun j =>
      Word.valuation (φ := dimensionSortMap f) x _
        ⟨⟨j.val, by simpa only [List.length_map] using j.isLt⟩, by
          simp [dimensionSortMap, Heterogeneous.dimensionWord, List.get_eq_getElem]⟩
    refine ⟨y, fun _ => Part.mem_some _, ?_⟩
    have he : Heterogeneous.dimensionFamily (f k) a y =
        Heterogeneous.dimensionFamily k a x := by
      funext j
      dsimp only [Heterogeneous.dimensionFamily, Equiv.coe_fn_mk]
      apply eq_of_heq
      apply HEq.trans (cast_heq _ _)
      dsimp only [y]
      apply HEq.trans (valuation_heq (φ := dimensionSortMap f) (A := B.carrier) x _)
      exact (cast_heq _ _).symm
    change q ∈ Part.some ((B.op σ).toFun (f k) _)
    rw [he]
    exact hq
  | @source j k h s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra)
      (Word.valuation (φ := dimensionSortMap f) x)
      ((heterogeneousDimensionDerivor sig f).image (.source h s))
    rw [heterogeneousDimensionDerivor_source]
    change q ∈ Part.some ((dimensionLE (B.sort s).str (f.monotone h.le)).source (x 0)) at hq
    by_cases hh : f j < f k
    · erw [dite_eq_left hh, Heterogeneous.eval_expansion_boundary,
        Term.partialEval_var, Part.bind_some]
      erw [dimensionLE_of_lt _ _ hh] at hq
      exact hq
    · erw [dite_eq_right hh, Term.partialEval_var]
      apply Part.mem_some_iff.mpr
      have he : f j = f k := le_antisymm (f.monotone h.le) (le_of_not_gt hh)
      exact eq_of_heq ((heq_of_eq (Part.mem_some_iff.mp hq)).trans
        ((dimensionLE_source_heq (B.sort s).str _ he (x 0)).trans
          (valuation_heq (φ := dimensionSortMap f) (A := B.carrier) x (s := (f j, s)) ⟨0, Prod.ext he.symm rfl⟩).symm))
  | @target j k h s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra)
      (Word.valuation (φ := dimensionSortMap f) x)
      ((heterogeneousDimensionDerivor sig f).image (.target h s))
    rw [heterogeneousDimensionDerivor_target]
    change q ∈ Part.some ((dimensionLE (B.sort s).str (f.monotone h.le)).target (x 0)) at hq
    by_cases hh : f j < f k
    · erw [dite_eq_left hh, Heterogeneous.eval_expansion_boundary,
        Term.partialEval_var, Part.bind_some]
      erw [dimensionLE_of_lt _ _ hh] at hq
      exact hq
    · erw [dite_eq_right hh, Term.partialEval_var]
      apply Part.mem_some_iff.mpr
      have he : f j = f k := le_antisymm (f.monotone h.le) (le_of_not_gt hh)
      exact eq_of_heq ((heq_of_eq (Part.mem_some_iff.mp hq)).trans
        ((dimensionLE_target_heq (B.sort s).str _ he (x 0)).trans
          (valuation_heq (φ := dimensionSortMap f) (A := B.carrier) x (s := (f j, s)) ⟨0, Prod.ext he.symm rfl⟩).symm))
  | @identity j k h s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra)
      (Word.valuation (φ := dimensionSortMap f) x)
      ((heterogeneousDimensionDerivor sig f).image (.identity h s))
    rw [heterogeneousDimensionDerivor_identity]
    change q ∈ Part.some ((dimensionLE (B.sort s).str (f.monotone h.le)).identity (x 0)) at hq
    by_cases hh : f j < f k
    · erw [dite_eq_left hh, Heterogeneous.eval_expansion_identity,
        Term.partialEval_var, Part.bind_some]
      erw [dimensionLE_of_lt _ _ hh] at hq
      exact hq
    · erw [dite_eq_right hh, Term.partialEval_var]
      apply Part.mem_some_iff.mpr
      have he : f j = f k := le_antisymm (f.monotone h.le) (le_of_not_gt hh)
      exact eq_of_heq ((heq_of_eq (Part.mem_some_iff.mp hq)).trans
        ((dimensionLE_identity_heq (B.sort s).str _ he (x 0)).trans
          (valuation_heq (φ := dimensionSortMap f) (A := B.carrier) x (s := (f k, s)) ⟨0, Prod.ext he rfl⟩).symm))
  | @comp j k h s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra)
      (Word.valuation (φ := dimensionSortMap f) x)
      ((heterogeneousDimensionDerivor sig f).image (.comp h s))
    rw [heterogeneousDimensionDerivor_comp]
    change q ∈ (dimensionLE (B.sort s).str (f.monotone h.le)).comp (x 0) (x 1) at hq
    by_cases hh : f j < f k
    · erw [dite_eq_left hh, Heterogeneous.partialEval_binary,
        Term.partialEval_var, Part.bind_some, Term.partialEval_var, Part.bind_some]
      erw [dimensionLE_of_lt _ _ hh] at hq
      exact hq
    · erw [dite_eq_right hh, Term.partialEval_var]
      have he : f j = f k := le_antisymm (f.monotone h.le) (le_of_not_gt hh)
      erw [dimensionLE_comp_of_eq _ _ he] at hq
      exact Part.mem_some_iff.mpr hq.2.symm

/-- Reindexing realizes the induced transformation, inserting only the empty-domain subtype. -/
noncomputable def heterogeneousDimensionRealization (hf : Saturating f)
    (B : Heterogeneous.CategorialAlgebra.{0, u, v, w} J sig) :
    (reindexedAlgebra B f hf).toPartialAlgebra ≅
      (heterogeneousDimension sig f).transformed B.toPartialAlgebra :=
  realizationIso (heterogeneousDimension sig f) B.toPartialAlgebra
    (reindexedAlgebra B f hf).toPartialAlgebra
    (Heterogeneous.equations_isEPAlgebra (reindexedAlgebra B f hf).satisfiesEquations)
    (heterogeneousDimensionCell sig f B.toPartialAlgebra)
    (heterogeneousDimensionCell_bijective sig f B.toPartialAlgebra)
    (reindexed_imageValue sig f hf B)

/-- The reindexing realization retains each underlying cell. -/
@[simp] theorem heterogeneousDimensionRealization_hom_val (hf : Saturating f)
    (B : Heterogeneous.CategorialAlgebra.{0, u, v, w} J sig) (p : I × S)
    (x : (reindexedAlgebra B f hf).carrier p) :
    ((heterogeneousDimensionRealization sig f hf B).hom.toMap p x).val = x := rfl

/-- A saturating dimension change preserves heterogeneous models. -/
theorem heterogeneousDimension_isModel (hf : Saturating f)
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol J sig))
    (hB : (Heterogeneous.specification J sig).IsModel B) :
    (Heterogeneous.specification I sig).IsModel ((heterogeneousDimension sig f).transformed B) := by
  let C := Heterogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = B := Heterogeneous.toPartialAlgebra_ofEquations B _
  rw [← hc]
  exact model_of_iso _ (heterogeneousDimensionRealization sig f hf C)
    ⟨Heterogeneous.equations_isEPAlgebra (reindexedAlgebra C f hf).satisfiesEquations,
      fun _ ⟨e, he⟩ => he ▸ (reindexedAlgebra C f hf).satisfiesEquations e⟩

end CategorialAlgebras.Dimensions
