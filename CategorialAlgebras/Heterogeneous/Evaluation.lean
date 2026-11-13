import CategorialAlgebras.Heterogeneous.Specification

/-!
# Evaluation in the heterogeneous signature

Unary and binary applications reduce to their arguments and basic partial operations.
These formulas make the domain specification and the contextual equations independent
of positional casts, and apply to carriers which need not be inhabited.
-/

universe i u v w x

namespace CategorialAlgebras
namespace Heterogeneous

variable {I : Type i} [Preorder I] {S : Type u} {sig : Signature.{u, v} S}

/-! ## Basic evaluation formulas -/

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
theorem partialEval_unary {X : I × S → Type x}
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (v : SortedSet.Map X A.carrier) {s t} (σ : Symbol I sig [s] t)
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
theorem partialEval_binary {X : I × S → Type x}
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (v : SortedSet.Map X A.carrier) {s} {j k : I} (h : j < k)
    (t r : Term (Symbol I sig) X (k, s)) :
    Term.partialEval v (binary h t r) =
      (Term.partialEval v t).bind (fun x =>
        (Term.partialEval v r).bind (fun y => A.op (.comp h s) (pair x y))) := by
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
@[simp] theorem partialEval_variables {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
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
@[simp] theorem satisfies_defined {X : I × S → Type x}
    (A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig))
    (v : SortedSet.Map X A.carrier) {s} (t : Term (Symbol I sig) X s) :
    EEquation.Satisfies A v (defined t) ↔ (Term.partialEval v t).Dom :=
  ⟨fun ⟨_, h, _⟩ => h.1, fun h => ⟨_, Part.get_mem h, Part.get_mem h⟩⟩

/-- Interpret a uniform context at an arbitrary tuple of elements of its sole sort. -/
def uniformValuation {A : S → Type w} {s m} (x : Fin m → A s) :
    SortedSet.Map (UniformVariables s m) A := fun _ ⟨j, ⟨h⟩⟩ => h ▸ x j

/-- Uniform variables evaluate to the entries of their tuple. -/
@[simp] theorem eval_uniform_variable
    (A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)) {s m}
    (x : Fin m → A.carrier s) (j : Fin m) :
    Term.partialEval (uniformValuation x) (variableTerm s j) = Part.some (x j) := rfl

/-- Transport of the output sort does not change satisfaction of an equation. -/
@[simp] theorem satisfies_transport {X : I × S → Type x}
    (A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig))
    (v : SortedSet.Map X A.carrier) {s t : I × S} (h : s = t)
    (e : EEquation (Symbol I sig) X s) :
    EEquation.Satisfies A v (h ▸ e) ↔ EEquation.Satisfies A v e := by
  cases h
  rfl

/-! ## Dimensional families and contexts -/

/-- Evaluation of an original symbol can use its original input positions. -/
theorem partialEval_base {X : I × S → Type x}
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (v : SortedSet.Map X A.carrier) (k : I) {a s} (σ : sig a s)
    (t : Word.Family (fun s => Term (Symbol I sig) X (k, s)) a) :
    Term.partialEval v (base k σ t) =
      (partFamily (fun j => Term.partialEval v (t j))).bind
        (fun z => A.op (.base k σ) ((dimensionFamily k a).symm z)) := by
  apply Part.ext
  intro q
  rw [base, Term.mem_partialEval_app, Part.mem_bind_iff]
  simp only [mem_partFamily]
  constructor
  · rintro ⟨r, hr, hq⟩
    refine ⟨dimensionFamily k a r, ?_, by simpa using hq⟩
    simpa using (dimensionFamily_rel (fun _ x t => x ∈ Term.partialEval v t) k a _ _).mp hr
  · rintro ⟨r, hr, hq⟩
    refine ⟨(dimensionFamily k a).symm r, ?_, hq⟩
    apply (dimensionFamily_rel (fun _ x t => x ∈ Term.partialEval v t) k a _ _).mpr
    simpa using hr

/-- Evaluation commutes with reindexing a family of everywhere defined terms. -/
theorem eval_dimension_family {X : I × S → Type x}
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (v : SortedSet.Map X A.carrier) (k : I) (a : List S)
    (t : Word.Family (Term (Symbol I sig) X) (dimensionWord k a))
    (r : Word.Family A.carrier (dimensionWord k a))
    (hr : ∀ p, Term.partialEval v (t p) = Part.some (r p)) (p : Fin a.length) :
    Term.partialEval v (dimensionFamily k a t p) = Part.some (dimensionFamily k a r p) := by
  have he := congrArg (dimensionFamily (A := fun s => Part (A.carrier s)) k a) (funext hr)
  rw [dimensionFamily_natural (fun s (t : Term (Symbol I sig) X s) => Term.partialEval v t),
    dimensionFamily_natural (fun s (r : A.carrier s) => Part.some r)] at he
  exact congrFun he p

omit [Preorder I] in
/-- A quantified predicate on dimensional families may use the original positions. -/
theorem dimensionFamily_all {A : I × S → Type w} (P : ∀ s, A s → Prop)
    (k : I) (a : List S) (r : Word.Family A (dimensionWord k a)) :
    (∀ p, P _ (r p)) ↔ ∀ p, P _ (dimensionFamily k a r p) :=
  dimensionFamily_rel (fun s x _ => P s x) k a r r

/-- Uniform contexts may be checked at arbitrary tuples of their single sort. -/
theorem uniform_valid_iff (A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig))
    {s m} {p : List (I × S)} {t}
    (prem : Word.Family (EEquation (Symbol I sig) (UniformVariables s m)) p)
    (concl : EEquation (Symbol I sig) (UniformVariables s m) t) :
    QEEquation.Valid A (uniformEquation s m prem concl).equation ↔
      ∀ x : Fin m → A.carrier s,
        (∀ j, EEquation.Satisfies A (uniformValuation x) (prem j)) →
          EEquation.Satisfies A (uniformValuation x) concl := by
  constructor
  · intro h x hx
    exact h (uniformValuation x) hx
  · intro h v hv
    have he : v = uniformValuation (fun j => v _ ⟨j, ⟨rfl⟩⟩) := by
      funext t ⟨j, ⟨ht⟩⟩
      cases ht
      rfl
    rw [he] at hv ⊢
    exact h _ hv

/-! ## Total operations from equations -/

/-- Source and target are total in every algebra satisfying the equations. -/
theorem boundary_total
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)} (hA : SatisfiesEquations A)
    {j k : I} (h : j < k) (s : S) (b : Bool) (x : A.carrier (k, s)) :
    (A.op (.boundary h s b) (single x)).Dom := by
  have hh := (uniform_valid_iff A _ _).mp (hA (.boundaryTotal h s b)) (fun _ => x)
    (fun p => Fin.elim0 p)
  have ht := (satisfies_defined A _ _).mp hh
  erw [boundary, partialEval_unary] at ht
  change ((Part.some x).bind (fun y => A.op (.boundary h s b) (single y))).Dom at ht
  rwa [Part.bind_some] at ht

/-- Identities are total in every algebra satisfying the equations. -/
theorem identity_total
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)} (hA : SatisfiesEquations A)
    {j k : I} (h : j < k) (s : S) (x : A.carrier (j, s)) :
    (A.op (.identity h s) (single x)).Dom := by
  have hh := (uniform_valid_iff A _ _).mp (hA (.identityTotal h s)) (fun _ => x)
    (fun p => Fin.elim0 p)
  have ht := (satisfies_defined A _ _).mp hh
  erw [identityTerm, partialEval_unary] at ht
  change ((Part.some x).bind (fun y => A.op (.identity h s) (single y))).Dom at ht
  rwa [Part.bind_some] at ht

/-- Every dimensional copy of an original symbol is total. -/
theorem base_total
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)} (hA : SatisfiesEquations A)
    (k : I) {a s} (σ : sig a s) (x : Word.Family A.carrier (dimensionWord k a)) :
    (A.op (.base k σ) x).Dom := by
  have hh := hA (.total k σ) (Word.valuation (φ := id) x) (fun p => Fin.elim0 p)
  change EEquation.Satisfies A _ (defined (.app (.base k σ) _)) at hh
  have ht := (satisfies_defined A _ _).mp hh
  erw [partialEval_variables (.base k σ) (Word.valuation (φ := id) x)] at ht
  exact ht

end Heterogeneous
end CategorialAlgebras
