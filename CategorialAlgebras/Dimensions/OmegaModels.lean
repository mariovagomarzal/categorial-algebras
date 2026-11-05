import CategorialAlgebras.Dimensions.OmegaStructure
import CategorialAlgebras.Dimensions.HomogeneousModels
import CategorialAlgebras.Dimensions.HeterogeneousModels

/-!
# Realizations and models of natural-dimensional changes

Explicit discrete extensions and algebras of cutoff cells realize the induced
transformations. In the homogeneous extension every cell is a cutoff cell.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S : Type u} (sig : Signature.{u, v} S) (n : ℕ)

/-- Insert the empty-domain subtype of a homogeneous discretization. -/
def omegaDiscretizationCell (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (s : S) (x : B.carrier s) : (homogeneousOmegaDiscretization sig n).Cell B s :=
  ⟨x, homogeneousOmegaDiscretization_isCell sig n B s x⟩

/-- Inserting the empty-domain subtype is bijective. -/
theorem omegaDiscretizationCell_bijective
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig)) (s : S) :
    Function.Bijective (omegaDiscretizationCell sig n B s) :=
  ⟨fun _ _ he => congrArg Subtype.val he, fun x => ⟨x.val, Subtype.ext rfl⟩⟩

/-- The explicit discretized operations have the prescribed term values. -/
theorem omegaDiscretized_imageValue (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : Homogeneous.Symbol ℕ sig a s)
    (x : Word.Family B.carrier a) {q}
    (hq : q ∈ (omegaDiscretizedAlgebra B).toPartialAlgebra.op σ x) :
    q ∈ (homogeneousOmegaDiscretization sig n).imageValue B.toPartialAlgebra σ
      (fun j => omegaDiscretizationCell sig n B.toPartialAlgebra _ (x j)) := by
  cases σ with
  | base σ =>
    apply (Term.mem_partialEval_app _ _ _ _).mpr
    exact ⟨x, fun _ => Part.mem_some _, hq⟩
  | source k s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra) (Word.valuation (φ := id) x)
      (if hk : k < n then Homogeneous.unary (.source ⟨k, hk⟩ s) (.var (Word.position _ 0)) else .var (Word.position _ 0))
    change q ∈ Part.some ((if hk : k < n then (B.sort s).str.dim ⟨k, hk⟩
      else Homogeneous.CategoryStructure.discrete _).source (x 0)) at hq
    by_cases hk : k < n
    · erw [dite_eq_left hk, Homogeneous.partialEval_unary, Term.partialEval_var,
        Part.bind_some]
      erw [dite_eq_left hk] at hq
      exact hq
    · erw [dite_eq_right hk, Term.partialEval_var]
      erw [dite_eq_right hk] at hq
      exact hq
  | target k s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra) (Word.valuation (φ := id) x)
      (if hk : k < n then Homogeneous.unary (.target ⟨k, hk⟩ s) (.var (Word.position _ 0)) else .var (Word.position _ 0))
    change q ∈ Part.some ((if hk : k < n then (B.sort s).str.dim ⟨k, hk⟩
      else Homogeneous.CategoryStructure.discrete _).target (x 0)) at hq
    by_cases hk : k < n
    · erw [dite_eq_left hk, Homogeneous.partialEval_unary, Term.partialEval_var,
        Part.bind_some]
      erw [dite_eq_left hk] at hq
      exact hq
    · erw [dite_eq_right hk, Term.partialEval_var]
      erw [dite_eq_right hk] at hq
      exact hq
  | comp k s =>
    change q ∈ Term.partialEval (A := B.toPartialAlgebra) (Word.valuation (φ := id) x)
      (if hk : k < n then Homogeneous.binary ⟨k, hk⟩ (.var (Word.position _ 0)) (.var (Word.position _ 1)) else .var (Word.position _ 0))
    change q ∈ (if hk : k < n then (B.sort s).str.dim ⟨k, hk⟩
      else Homogeneous.CategoryStructure.discrete _).comp (x 0) (x 1) at hq
    by_cases hk : k < n
    · erw [dite_eq_left hk, Homogeneous.partialEval_binary, Term.partialEval_var,
        Part.bind_some, Term.partialEval_var, Part.bind_some]
      erw [dite_eq_left hk] at hq
      exact hq
    · erw [dite_eq_right hk, Term.partialEval_var]
      erw [dite_eq_right hk] at hq
      exact Part.mem_some_iff.mpr hq.2.symm

/-- The explicit discretization realizes the induced transformation by inserting only
the empty-domain subtype. -/
noncomputable def homogeneousOmegaDiscretizationRealization
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    (omegaDiscretizedAlgebra B).toPartialAlgebra ≅
      (homogeneousOmegaDiscretization sig n).transformed B.toPartialAlgebra :=
  realizationIso (homogeneousOmegaDiscretization sig n) B.toPartialAlgebra
    (omegaDiscretizedAlgebra B).toPartialAlgebra
    (Homogeneous.equations_isEPAlgebra (omegaDiscretizedAlgebra B).satisfiesEquations)
    (omegaDiscretizationCell sig n B.toPartialAlgebra)
    (omegaDiscretizationCell_bijective sig n B.toPartialAlgebra) (omegaDiscretized_imageValue sig n B)

/-- The discretization realization retains each underlying element. -/
@[simp] theorem homogeneousOmegaDiscretizationRealization_hom_val
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) (s : S) (x : B.carrier s) :
    ((homogeneousOmegaDiscretizationRealization sig n B).hom.toMap s x).val = x := rfl

/-- Discretization sends homogeneous models to homogeneous models. -/
theorem homogeneousOmegaDiscretization_isModel
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    (Homogeneous.specification ℕ sig).IsModel
      ((homogeneousOmegaDiscretization sig n).transformed B) := by
  let C := Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = B := Homogeneous.toPartialAlgebra_ofEquations B _
  rw [← hc]
  exact model_of_iso _ (homogeneousOmegaDiscretizationRealization sig n C)
    ⟨Homogeneous.equations_isEPAlgebra (omegaDiscretizedAlgebra C).satisfiesEquations,
      fun _ ⟨e, he⟩ => he ▸ (omegaDiscretizedAlgebra C).satisfiesEquations e⟩

/-- In an expansion the infinite truncation selects exactly the $n$-cells. -/
theorem homogeneousOmegaTruncation_isCell_iff
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (s : S) (x : B.carrier s) :
    (homogeneousOmegaTruncation sig n).IsCell B.toPartialAlgebra s x ↔
      (B.sort s).str.IsCell n x := by
  constructor
  · intro hx
    obtain ⟨q, hq, hr⟩ := hx s (omegaTruncationEquation sig n s) ⟨rfl, rfl⟩
    have he : q = x := Part.mem_some_iff.mp hq
    change q ∈ Term.partialEval _ (Homogeneous.unary _ _) at hr
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some] at hr
    exact (Part.mem_some_iff.mp hr).symm.trans he
  · intro hx t e ⟨ht, he⟩
    cases ht
    cases he
    refine ⟨x, Part.mem_some _, ?_⟩
    change x ∈ Term.partialEval (A := B.toPartialAlgebra)
      (Word.singletonValuation x) (Homogeneous.unary (.source n s) (.var (Word.position _ 0)))
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some_iff.mpr hx.symm

/-- The finite construction of the truncated carrier also selects the original $n$-cells. -/
theorem omegaTruncatedAlgebra_cell
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (s : S)
    (x : (omegaTruncatedAlgebra B n).carrier s) :
    (B.sort s).str.IsCell n x.val := by
  have hx := (homogeneousTruncation_isCell_iff sig (Nat.le_succ n)
    (omegaRestrictedAlgebra B (n + 1)) s x.val).mp x.property
  exact hx (Nat.lt_succ_self n)

/-- Insert a finite-construction cutoff cell into the infinite truncation subtype. -/
def omegaTruncationCell
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (s : S)
    (x : (omegaTruncatedAlgebra B n).carrier s) :
    (homogeneousOmegaTruncation sig n).Cell B.toPartialAlgebra s :=
  ⟨x.val, (homogeneousOmegaTruncation_isCell_iff sig n B s x.val).mpr
    (omegaTruncatedAlgebra_cell sig n B s x)⟩

/-- The finite and infinite cutoff subtypes have precisely the same elements. -/
theorem omegaTruncationCell_bijective
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (s : S) :
    Function.Bijective (omegaTruncationCell sig n B s) := by
  refine ⟨?_, fun x => ?_⟩
  · intro x y h
    exact Subtype.ext (congrArg (fun z : (homogeneousOmegaTruncation sig n).Cell B.toPartialAlgebra s => z.val) h)
  · have hx := (homogeneousOmegaTruncation_isCell_iff sig n B s x.val).mp x.property
    refine ⟨⟨x.val, (homogeneousTruncation_isCell_iff sig (Nat.le_succ n)
      (omegaRestrictedAlgebra B (n + 1)) s x.val).mpr (fun _ => hx)⟩, Subtype.ext rfl⟩

/-- The algebra of cutoff cells has the prescribed original operation values. -/
theorem omegaTruncated_imageValue
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    {a s} (σ : Homogeneous.Symbol (Fin n) sig a s)
    (x : Word.Family (omegaTruncatedAlgebra B n).carrier a) {q}
    (hq : q ∈ (omegaTruncatedAlgebra B n).toPartialAlgebra.op σ x) :
    (omegaTruncationCell sig n B s q).val ∈
      (homogeneousOmegaTruncation sig n).imageValue B.toPartialAlgebra σ
        (fun j => omegaTruncationCell sig n B _ (x j)) := by
  have hv := truncated_imageValue sig (Nat.le_succ n)
    (omegaRestrictedAlgebra B (n + 1)) σ x hq
  cases σ with
  | base σ => exact hv
  | source k s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.unary _ _) at hv
    change q.val ∈ Term.partialEval (A := B.toPartialAlgebra)
      (Word.valuation (φ := id) (fun j => (x j).val))
      (Homogeneous.unary (.source k.val s) (.var (Word.position _ 0)))
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some] at hv ⊢
    exact hv
  | target k s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.unary _ _) at hv
    change q.val ∈ Term.partialEval (A := B.toPartialAlgebra)
      (Word.valuation (φ := id) (fun j => (x j).val))
      (Homogeneous.unary (.target k.val s) (.var (Word.position _ 0)))
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some] at hv ⊢
    exact hv
  | comp k s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.binary _ _ _) at hv
    change q.val ∈ Term.partialEval (A := B.toPartialAlgebra)
      (Word.valuation (φ := id) (fun j => (x j).val))
      (Homogeneous.binary k.val (.var (Word.position _ 0)) (.var (Word.position _ 1)))
    erw [Homogeneous.partialEval_binary, Term.partialEval_var, Part.bind_some,
      Term.partialEval_var, Part.bind_some] at hv ⊢
    exact hv

/-- Infinite truncation is realized by the algebra of cutoff cells. -/
noncomputable def homogeneousOmegaTruncationRealization
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) :
    (omegaTruncatedAlgebra B n).toPartialAlgebra ≅
      (homogeneousOmegaTruncation sig n).transformed B.toPartialAlgebra :=
  realizationIso (homogeneousOmegaTruncation sig n) B.toPartialAlgebra
    (omegaTruncatedAlgebra B n).toPartialAlgebra
    (Homogeneous.equations_isEPAlgebra (omegaTruncatedAlgebra B n).satisfiesEquations)
    (omegaTruncationCell sig n B) (omegaTruncationCell_bijective sig n B)
    (omegaTruncated_imageValue sig n B)

/-- Truncation preserves all homogeneous models, without requiring finite cells. -/
theorem homogeneousOmegaTruncation_isModel
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) :
    (Homogeneous.specification (Fin n) sig).IsModel
      ((homogeneousOmegaTruncation sig n).transformed B) := by
  let C := Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = B := Homogeneous.toPartialAlgebra_ofEquations B _
  rw [← hc]
  exact model_of_iso _ (homogeneousOmegaTruncationRealization sig n C)
    ⟨Homogeneous.equations_isEPAlgebra (omegaTruncatedAlgebra C n).satisfiesEquations,
      fun _ ⟨e, he⟩ => he ▸ (omegaTruncatedAlgebra C n).satisfiesEquations e⟩

/-- Every transformed homogeneous cell is an $n$-cell, expressed in the partial signature. -/
theorem homogeneousOmegaDiscretization_cutoff
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) (s : S)
    (x : ((homogeneousOmegaDiscretization sig n).transformed B).carrier s) :
    x ∈ ((homogeneousOmegaDiscretization sig n).transformed B).op
      (.source n s) (Homogeneous.single x) := by
  let C := Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = B := Homogeneous.toPartialAlgebra_ofEquations B _
  revert x
  rw [← hc]
  intro x
  let e := homogeneousOmegaDiscretizationRealization sig n C
  let y := e.inv.toMap s x
  have hy : y ∈ (omegaDiscretizedAlgebra C).toPartialAlgebra.op
      (.source n s) (Homogeneous.single y) :=
    Part.mem_some_iff.mpr (omegaDiscretizedAlgebra_isCell C s y).symm
  have he : e.hom.toMap s y = x :=
    congrArg (fun f => PartialAlgebra.Hom.toMap f s x) e.inv_hom_id
  have hm := e.hom.map_op (.source n s) (Homogeneous.single y) hy
  have hf : (fun j => e.hom.toMap ([s].get j) (Homogeneous.single y j)) =
      Homogeneous.single x := by
    funext j
    fin_cases j
    exact he
  rw [hf, he] at hm
  exact hm

/-- The homogeneous discretization lands in finite-dimensional models. -/
theorem homogeneousOmegaDiscretization_finite
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    Homogeneous.FiniteCells ((homogeneousOmegaDiscretization sig n).transformed B) :=
  fun s x => ⟨n, homogeneousOmegaDiscretization_cutoff sig n B hB s x⟩

/-- Clamping natural dimensions is saturating. -/
theorem omegaClamp_saturating : Saturating (omegaClamp n) := by
  intro i j k hij hjk he
  apply Fin.ext
  have hv := congrArg Fin.val he
  change min i n = min j n at hv
  change min j n = min k n
  omega

/-- Heterogeneous truncation preserves models. -/
theorem heterogeneousOmegaTruncation_isModel
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B) :
    (Heterogeneous.specification (Fin (n + 1)) sig).IsModel
      ((heterogeneousOmegaTruncation sig n).transformed B) :=
  heterogeneousDimension_isModel sig _ (orderEmbedding_saturating _) B hB

/-- Heterogeneous discretization preserves models. -/
theorem heterogeneousOmegaDiscretization_isModel
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B) :
    (Heterogeneous.specification ℕ sig).IsModel
      ((heterogeneousOmegaDiscretization sig n).transformed B) :=
  heterogeneousDimension_isModel sig _ (omegaClamp_saturating n) B hB

end CategorialAlgebras.Dimensions
