import CategorialAlgebras.Homogeneous.Recovery

/-!
# Validity of the homogeneous equations

Expansion of a categorial algebra satisfies every contextual equation. Together with
recovery, this gives the two directions of the presentation on unchanged carriers.
-/

universe i u v w x

namespace CategorialAlgebras
namespace Homogeneous

variable {I : Type i} [LT I] {S : Type u} {sig : Signature.{u, v} S}

/-- Select a source or target map in a categorial algebra. -/
def CategorialAlgebra.boundary (A : CategorialAlgebra.{i, u, v, w} I sig)
    (k : I) (b : Bool) {s} (x : A.carrier s) : A.carrier s :=
  if b then ((A.sort s).str.dim k).target x else ((A.sort s).str.dim k).source x

/-- All boundaries in one dimension fix each other's images. -/
theorem CategorialAlgebra.boundary_retract (A : CategorialAlgebra.{i, u, v, w} I sig)
    (k : I) (b c : Bool) {s} (x : A.carrier s) :
    A.boundary k b (A.boundary k c x) = A.boundary k c x := by
  cases b <;> cases c
  · exact ((A.sort s).str.dim k).source_source x
  · exact ((A.sort s).str.dim k).source_target x
  · exact ((A.sort s).str.dim k).target_source x
  · exact ((A.sort s).str.dim k).target_target x

/-- Boundaries of a composite are its outer boundaries. -/
theorem CategorialAlgebra.boundary_comp (A : CategorialAlgebra.{i, u, v, w} I sig)
    (k : I) (b : Bool) {s} {x y z : A.carrier s}
    (hz : z ∈ ((A.sort s).str.dim k).comp x y) :
    A.boundary k b z = A.boundary k b (if b then x else y) := by
  cases b
  · exact ((A.sort s).str.dim k).source_comp _ _ _ hz
  · exact ((A.sort s).str.dim k).target_comp _ _ _ hz

/-- Higher boundaries fix the corresponding lower boundaries. -/
theorem CategorialAlgebra.higher_lower (A : CategorialAlgebra.{i, u, v, w} I sig)
    {l k : I} (h : l < k) (b : Bool) {s} (x : A.carrier s) :
    A.boundary k b (A.boundary l b x) = A.boundary l b x := by
  cases b
  · exact ((A.sort s).str.compatible l k h).source_source x
  · exact ((A.sort s).str.compatible l k h).target_target x

/-- Lower boundaries absorb either higher boundary. -/
theorem CategorialAlgebra.lower_higher (A : CategorialAlgebra.{i, u, v, w} I sig)
    {l k : I} (h : l < k) (b c : Bool) {s} (x : A.carrier s) :
    A.boundary l b (A.boundary k c x) = A.boundary l b x := by
  cases b <;> cases c
  · exact ((A.sort s).str.compatible l k h).source_source_low x
  · exact ((A.sort s).str.compatible l k h).source_target x
  · exact ((A.sort s).str.compatible l k h).target_source x
  · exact ((A.sort s).str.compatible l k h).target_target_low x

/-- Higher boundaries preserve lower composite values. -/
theorem CategorialAlgebra.higher_comp (A : CategorialAlgebra.{i, u, v, w} I sig)
    {l k : I} (h : l < k) (b : Bool) {s} {x y z : A.carrier s}
    (hz : z ∈ ((A.sort s).str.dim l).comp x y) :
    A.boundary k b z ∈ ((A.sort s).str.dim l).comp (A.boundary k b x) (A.boundary k b y) := by
  cases b
  · exact ((A.sort s).str.compatible l k h).source_comp _ _ _ hz
  · exact ((A.sort s).str.compatible l k h).target_comp _ _ _ hz

/-- Original operations preserve both kinds of boundary. -/
theorem CategorialAlgebra.operation_boundary (A : CategorialAlgebra.{i, u, v, w} I sig)
    {a s} (σ : sig a s) (k : I) (b : Bool) (x : Word.Family A.carrier a) :
    A.boundary k b ((A.op σ).toFun x) =
      (A.op σ).toFun (fun j => A.boundary k b (x j)) := by
  cases b
  · exact ((A.op σ).map_source k x).symm
  · exact ((A.op σ).map_target k x).symm

/-- Boundary evaluation in an expanded categorial algebra. -/
theorem eval_expansion_boundary {X : S → Type x}
    (A : CategorialAlgebra.{i, u, v, w} I sig) (v : SortedSet.Map X A.carrier)
    (k : I) (b : Bool) {s} (t : Term (Symbol I sig) X s) :
    Term.partialEval (A := A.toPartialAlgebra) v (boundary k b t) =
      (Term.partialEval (A := A.toPartialAlgebra) v t).bind
        (fun x => Part.some (A.boundary k b x)) := by
  erw [boundary, partialEval_unary]
  congr 1
  funext x
  cases b <;> rfl

/-- Original operation evaluation in an expanded categorial algebra. -/
theorem eval_expansion_base {X : S → Type x}
    (A : CategorialAlgebra.{i, u, v, w} I sig) (v : SortedSet.Map X A.carrier)
    {a s} (σ : sig a s) (t : Word.Family (Term (Symbol I sig) X) a) :
    Term.partialEval (A := A.toPartialAlgebra) v (.app (.base σ) t) =
      (partFamily (fun j => Term.partialEval (A := A.toPartialAlgebra) v (t j))).bind
        (fun z => Part.some ((A.op σ).toFun z)) := rfl

/-- Uniform binary terms evaluate to the corresponding categorical composition. -/
theorem eval_expansion_binary (A : CategorialAlgebra.{i, u, v, w} I sig)
    {s m} (x : Fin m → A.carrier s) (k : I) (j j' : Fin m) :
    Term.partialEval (A := A.toPartialAlgebra) (uniformValuation x)
      (binary k (variableTerm s j) (variableTerm s j')) =
      ((A.sort s).str.dim k).comp (x j) (x j') := by
  erw [partialEval_binary]
  simp only [eval_uniform_variable, Part.bind_some]
  rfl

/-- All contextual equations hold in the expansion of a categorial algebra. -/
theorem CategorialAlgebra.satisfiesEquations (A : CategorialAlgebra.{i, u, v, w} I sig) :
    SatisfiesEquations A.toPartialAlgebra := by
  intro e
  cases e with
  | total σ =>
    intro v _
    apply (satisfies_defined _ _ _).mpr
    erw [partialEval_variables]
    exact Part.some_dom _
  | boundaryTotal k s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    apply (satisfies_defined _ _ _).mpr
    erw [eval_expansion_boundary]
    simp only [eval_uniform_variable, Part.bind_some, Part.some_dom]
  | retract k s b c =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left, A.boundary_retract]
  | domainForward k s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := (satisfies_defined _ _ _).mp (hx 0)
    erw [eval_expansion_binary] at hd
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left]
    exact (((A.sort s).str.dim k).comp_dom _ _).mp hd
  | domainBackward k s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := hx 0
    unfold EEquation.Satisfies at hd
    simp only [eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left] at hd
    apply (satisfies_defined _ _ _).mpr
    erw [eval_expansion_binary]
    exact (((A.sort s).str.dim k).comp_dom _ _).mpr hd
  | compositeBoundary k s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := (satisfies_defined _ _ _).mp (hx 0)
    erw [eval_expansion_binary] at hd
    let z := (((A.sort s).str.dim k).comp (x 0) (x 1)).get hd
    have hz : z ∈ ((A.sort s).str.dim k).comp (x 0) (x 1) := Part.get_mem hd
    unfold EEquation.Satisfies
    cases b <;>
      simp only [Bool.false_eq_true, ↓reduceIte, eval_expansion_boundary,
        eval_expansion_binary, eval_uniform_variable, Part.bind_some,
        Part.mem_bind_iff, Part.mem_some_iff]
    · exact ⟨_, ⟨z, hz, rfl⟩, A.boundary_comp k false hz⟩
    · exact ⟨_, ⟨z, hz, rfl⟩, A.boundary_comp k true hz⟩
  | unit k s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    unfold EEquation.Satisfies
    cases b <;>
      simp only [Bool.false_eq_true, ↓reduceIte, partialEval_binary,
        eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
        Part.mem_some_iff, exists_eq_right]
    · exact ((A.sort s).str.dim k).comp_source _
    · exact ((A.sort s).str.dim k).target_comp_self _
  | assoc k s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hxy := (satisfies_defined _ _ _).mp (hx 0)
    have hyz := (satisfies_defined _ _ _).mp (hx 1)
    erw [eval_expansion_binary] at hxy hyz
    obtain ⟨q, hq, hq'⟩ := ((A.sort s).str.dim k).assoc _ _ _ _ _
      (Part.get_mem hxy) (Part.get_mem hyz)
    unfold EEquation.Satisfies
    simp only [partialEval_binary, eval_uniform_variable, Part.bind_some, Part.mem_bind_iff]
    exact ⟨q, ⟨_, Part.get_mem hxy, hq⟩, _, Part.get_mem hyz, hq'⟩
  | higherLower l k h s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left, A.higher_lower h]
  | lowerHigher l k h s b c =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left, A.lower_higher h]
  | boundaryComposition l k h s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := (satisfies_defined _ _ _).mp (hx 0)
    erw [eval_expansion_binary] at hd
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, partialEval_binary, eval_uniform_variable,
      Part.bind_some, Part.mem_bind_iff, Part.mem_some_iff]
    exact ⟨_, ⟨_, Part.get_mem hd, rfl⟩, A.higher_comp h b (Part.get_mem hd)⟩
  | interchange l k h s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hxy := (satisfies_defined _ _ _).mp (hx 0)
    have hzt := (satisfies_defined _ _ _).mp (hx 1)
    have hxz := (satisfies_defined _ _ _).mp (hx 2)
    have hyt := (satisfies_defined _ _ _).mp (hx 3)
    erw [eval_expansion_binary] at hxy hzt hxz hyt
    obtain ⟨q, hq, hq'⟩ := ((A.sort s).str.compatible l k h).interchange _ _ _ _ _ _ _ _
      (Part.get_mem hxy) (Part.get_mem hzt) (Part.get_mem hxz) (Part.get_mem hyt)
    unfold EEquation.Satisfies
    simp only [partialEval_binary, eval_uniform_variable, Part.bind_some, Part.mem_bind_iff]
    exact ⟨q, ⟨_, Part.get_mem hxy, _, Part.get_mem hzt, hq⟩,
      _, Part.get_mem hxz, _, Part.get_mem hyt, hq'⟩
  | operationBoundary σ k b =>
    dsimp only [Axiom.equation, contextualEquation]
    intro v _
    change EEquation.Satisfies A.toPartialAlgebra v
      (Homogeneous.boundary k b (.app (.base σ) _), .app (.base σ) _)
    unfold EEquation.Satisfies
    erw [eval_expansion_boundary, eval_expansion_base, eval_expansion_base]
    have ht j : Term.partialEval (A := A.toPartialAlgebra) v
        (Homogeneous.boundary k b (.var (Word.position _ j))) =
        Part.some (A.boundary k b (v _ (Word.position _ j))) := by
      erw [eval_expansion_boundary]
      exact Part.bind_some _ _
    simp_rw [ht]
    simp only [Term.partialEval, partFamily_some, Part.bind_some, Part.mem_some_iff,
      exists_eq_left, A.operation_boundary]
  | operationComposition σ k =>
    dsimp only [Axiom.equation, contextualEquation]
    intro v hv
    have hc j := (satisfies_defined _ _ _).mp (hv j)
    simp only [partialEval_binary, Term.partialEval, Part.bind_some] at hc
    let z j := ((A.sort _).str.dim k).comp
      (v _ (Word.position _ j, false)) (v _ (Word.position _ j, true))
    have hd j : (z j).Dom := hc j
    have hm := (A.op σ).map_comp k _ _ _
      ((mem_partFamily _ _).mpr (fun j => Part.get_mem (hd j)))
    change EEquation.Satisfies A.toPartialAlgebra v
      (.app (.base σ) _, binary k (.app (.base σ) _) _)
    unfold EEquation.Satisfies
    erw [eval_expansion_base, partialEval_binary, eval_expansion_base, eval_expansion_base]
    have hf : partFamily (fun j => Term.partialEval (A := A.toPartialAlgebra) v
        (binary k (.var (Word.position _ j, false)) (.var (Word.position _ j, true)))) =
        Part.some (fun j => (z j).get (hd j)) := by
      apply Part.eq_some_iff.mpr
      apply (mem_partFamily _ _).mpr
      intro j
      erw [partialEval_binary]
      simp only [Term.partialEval, Part.bind_some]
      exact Part.get_mem (hd j)
    erw [hf, Part.bind_some]
    simp only [Term.partialEval, partFamily_some, Part.bind_some, Part.mem_some_iff,
      exists_eq_left]
    exact hm

end Homogeneous
end CategorialAlgebras
