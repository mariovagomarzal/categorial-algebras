import CategorialAlgebras.Homogeneous.Specification

/-!
# Evaluation in the homogeneous signature

Unary and binary applications reduce to their arguments and basic partial operations.
These formulas make the domain specification and the contextual equations independent
of positional casts, and apply to carriers which need not be inhabited.
-/

universe i u v w x

namespace CategorialAlgebras
namespace Homogeneous

variable {I : Type i} {S : Type u} {sig : Signature.{u, v} S}

/-- A family of defined values assembles to its defined function. -/
@[simp] theorem partFamily_some {J : Type x} {A : J → Type w} (x : ∀ j, A j) :
    partFamily (fun j => Part.some (x j)) = Part.some x := by
  apply Part.ext
  intro y
  simp only [mem_partFamily, Part.mem_some_iff, funext_iff]

/-- A one-entry sorted family. -/
def single {A : S → Type w} {s} (x : A s) : Word.Family A [s] :=
  Fin.cases x (fun j => Fin.elim0 j)

/-- A two-entry sorted family. -/
def pair {A : S → Type w} {s} (x y : A s) : Word.Family A [s, s] :=
  Fin.cases x (Fin.cases y (fun j => Fin.elim0 j))

/-- A one-entry family is determined by its only value. -/
@[simp] theorem single_eta {A : S → Type w} {s} (x : Word.Family A [s]) :
    single (x 0) = x := by funext j; fin_cases j; rfl

/-- A two-entry family is determined by its two values. -/
@[simp] theorem pair_eta {A : S → Type w} {s} (x : Word.Family A [s, s]) :
    pair (x 0) (x 1) = x := by funext j; fin_cases j <;> rfl

/-- Evaluate a unary application by first evaluating its only argument. -/
theorem partialEval_unary {X : S → Type x}
    {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (v : SortedSet.Map X A.carrier) {s} (σ : Symbol I sig [s] s)
    (t : Term (Symbol I sig) X s) :
    Term.partialEval v (unary σ t) =
      (Term.partialEval v t).bind (fun x => A.op σ (single x)) := by
  apply Part.ext
  intro q
  rw [unary, Term.mem_partialEval_app, Part.mem_bind_iff]
  constructor
  · rintro ⟨r, hr, hq⟩
    exact ⟨r 0, hr 0, by erw [single_eta]; exact hq⟩
  · rintro ⟨r, hr, hq⟩
    refine ⟨single r, ?_, hq⟩
    intro j
    fin_cases j
    exact hr

/-- Evaluate a binary application by first evaluating both arguments. -/
theorem partialEval_binary {X : S → Type x}
    {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (v : SortedSet.Map X A.carrier) {s} (k : I)
    (t r : Term (Symbol I sig) X s) :
    Term.partialEval v (binary k t r) =
      (Term.partialEval v t).bind (fun x =>
        (Term.partialEval v r).bind (fun y => A.op (.comp k s) (pair x y))) := by
  apply Part.ext
  intro q
  rw [binary, Term.mem_partialEval_app, Part.mem_bind_iff]
  simp only [Part.mem_bind_iff]
  constructor
  · rintro ⟨z, hz, hq⟩
    exact ⟨z 0, hz 0, z 1, hz 1, by erw [pair_eta]; exact hq⟩
  · rintro ⟨x, hx, y, hy, hq⟩
    refine ⟨pair x y, ?_, hq⟩
    intro j
    fin_cases j
    · exact hx
    · exact hy

/-- Evaluate an application to variables as the corresponding basic operation. -/
@[simp] theorem partialEval_variables {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    {a s} (σ : Symbol I sig a s) (v : SortedSet.Map (Word.Variables a) A.carrier) :
    Term.partialEval v (.app σ (fun j => .var (Word.position a j))) =
      A.op σ (fun j => v _ (Word.position a j)) := by
  apply Part.ext
  intro q
  simp only [Term.mem_partialEval_app, Term.partialEval_var, Part.mem_some_iff]
  constructor
  · rintro ⟨r, hr, hq⟩
    have he : r = fun j => v _ (Word.position a j) := funext hr
    rwa [he] at hq
  · intro hq
    exact ⟨_, fun _ => rfl, hq⟩

/-- An existence assertion is equivalent to definedness of the term. -/
@[simp] theorem satisfies_defined {X : S → Type x}
    (A : PartialAlgebra.{u, max i v u, w} (Symbol I sig))
    (v : SortedSet.Map X A.carrier) {s} (t : Term (Symbol I sig) X s) :
    EEquation.Satisfies A v (defined t) ↔ (Term.partialEval v t).Dom :=
  ⟨fun ⟨_, h, _⟩ => h.1, fun h => ⟨_, Part.get_mem h, Part.get_mem h⟩⟩

/-- Interpret a uniform context at an arbitrary tuple of elements of its sole sort. -/
def uniformValuation {A : S → Type w} {s m} (x : Fin m → A s) :
    SortedSet.Map (UniformVariables s m) A := fun _ ⟨j, ⟨h⟩⟩ => h ▸ x j

/-- Uniform variables evaluate to the entries of their tuple. -/
@[simp] theorem eval_uniform_variable
    (A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)) {s m}
    (x : Fin m → A.carrier s) (j : Fin m) :
    Term.partialEval (uniformValuation x) (variableTerm s j) = Part.some (x j) := rfl

/-- Transport of the output sort does not change satisfaction of an equation. -/
@[simp] theorem satisfies_transport {X : S → Type x}
    (A : PartialAlgebra.{u, max i v u, w} (Symbol I sig))
    (v : SortedSet.Map X A.carrier) {s t : S} (h : s = t)
    (e : EEquation (Symbol I sig) X s) :
    EEquation.Satisfies A v (h ▸ e) ↔ EEquation.Satisfies A v e := by
  cases h
  rfl

/-- Validity of a uniform contextual equation can be used at any tuple of its sort. -/
theorem uniform_valid_iff (A : PartialAlgebra.{u, max i v u, w} (Symbol I sig))
    {s m p} (prem : Fin p → EEquation (Symbol I sig) (UniformVariables s m) s)
    (concl : EEquation (Symbol I sig) (UniformVariables s m) s) :
    QEEquation.Valid A (uniformEquation s m p prem concl).equation ↔
      ∀ x : Fin m → A.carrier s,
        (∀ j, EEquation.Satisfies A (uniformValuation x) (prem j)) →
          EEquation.Satisfies A (uniformValuation x) concl := by
  constructor
  · intro h x hx
    apply h (uniformValuation x)
    intro j
    change Fin (List.replicate p s).length at j
    exact (satisfies_transport A _
      (show (List.replicate p s).get j = s by simp).symm
      (prem (Fin.cast (List.length_replicate ..) j))).mpr
        (hx (Fin.cast (List.length_replicate ..) j))
  · intro h v hv
    have he : v = uniformValuation (fun j => v _ ⟨j, ⟨rfl⟩⟩) := by
      funext t ⟨j, ⟨ht⟩⟩
      cases ht
      rfl
    rw [he] at hv ⊢
    apply h
    intro j
    simpa [uniformEquation] using hv (Fin.cast (List.length_replicate ..).symm j)

/-- Source and target are total in every algebra satisfying the contextual equations. -/
theorem boundary_total [LT I]
    {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)} (h : SatisfiesEquations A)
    (k : I) (s : S) (b : Bool) (x : A.carrier s) :
    (A.op (.boundary k s b) (single x)).Dom := by
  have hh := (uniform_valid_iff A _ _).mp (h (.boundaryTotal k s b)) (fun _ => x)
    (fun j => Fin.elim0 j)
  have ht := (satisfies_defined A _ _).mp hh
  erw [boundary, partialEval_unary] at ht
  change ((Part.some x).bind (fun y => A.op (.boundary k s b) (single y))).Dom at ht
  rwa [Part.bind_some] at ht

/-- The original symbols are total in every algebra satisfying the contextual equations. -/
theorem base_total [LT I]
    {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)} (h : SatisfiesEquations A)
    {a s} (σ : sig a s) (x : Word.Family A.carrier a) : (A.op (.base σ) x).Dom := by
  have hh := h (.total σ) (Word.valuation (φ := id) x) (fun j => Fin.elim0 j)
  change EEquation.Satisfies A _ (defined (.app (.base σ) _)) at hh
  have ht := (satisfies_defined A _ _).mp hh
  erw [partialEval_variables (.base σ) (Word.valuation (φ := id) x)] at ht
  exact ht

end Homogeneous
end CategorialAlgebras
