import CategorialAlgebras.Homogeneous.Algebra
import CategorialAlgebras.HepDerivor.Signature
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# The homogeneous categorial signature

The original symbols are extended by source, target and composition at every dimension.
Only composition has a domain condition: equality of source and target. Dependencies
have height at most one, so this equationally partial signature is hierarchical.
-/

universe i u v w x

namespace CategorialAlgebras
namespace Homogeneous

/-- The enlarged signature, with disjoint constructors for all symbol families. -/
inductive Symbol (I : Type i) {S : Type u} (sig : Signature.{u, v} S) : List S → S → Type (max i v u)
  /-- An original operation. -/
  | base {a s} : sig a s → Symbol I sig a s
  /-- Source at a dimension and sort. -/
  | source (k : I) (s : S) : Symbol I sig [s] s
  /-- Target at a dimension and sort. -/
  | target (k : I) (s : S) : Symbol I sig [s] s
  /-- Composition at a dimension and sort. -/
  | comp (k : I) (s : S) : Symbol I sig [s, s] s

variable {I : Type i} {S : Type u} {sig : Signature.{u, v} S}

/-- A source or target symbol, selected by a Boolean (`false` means source). -/
def Symbol.boundary (k : I) (s : S) (b : Bool) : Symbol I sig [s] s :=
  if b then .target k s else .source k s

/-- Apply a unary homogeneous symbol to a term. -/
def unary {X : S → Type x} {s} (σ : Symbol I sig [s] s)
    (t : Term (Symbol I sig) X s) : Term (Symbol I sig) X s :=
  .app σ (Fin.cases t (fun j => Fin.elim0 j))

/-- Apply a composition symbol to two terms. -/
def binary {X : S → Type x} (k : I) {s} (t r : Term (Symbol I sig) X s) :
    Term (Symbol I sig) X s :=
  .app (.comp k s) (Fin.cases t (Fin.cases r (fun j => Fin.elim0 j)))

/-- Apply a boundary symbol to a term. -/
def boundary {X : S → Type x} (k : I) (b : Bool) {s}
    (t : Term (Symbol I sig) X s) : Term (Symbol I sig) X s :=
  unary (.boundary k s b) t

/-- A single existence equation, as a sorted set. -/
def singletonEquation {σ : Signature.{u, v} S} {X : S → Type x} {s}
    (e : EEquation σ X s) : EEquationSet σ X :=
  fun t => {e' | ∃ h : s = t, e' = h ▸ e}

/-- The existence equation expressing the domain of a composition. -/
def compositionDomain (k : I) (s : S) : EEquation (Symbol I sig) (Word.Variables [s, s]) s :=
  (boundary k false (.var (Word.position [s, s] 0)),
    boundary k true (.var (Word.position [s, s] 1)))

/-- The homogeneous ep-signature: only composition has a domain condition. -/
def epSignature (I : Type i) {S : Type u} (sig : Signature.{u, v} S) : EPSignature S where
  symbol := Symbol I sig
  domain
    | .base _ => fun _ => ∅
    | .source _ _ => fun _ => ∅
    | .target _ _ => fun _ => ∅
    | .comp k s => singletonEquation (compositionDomain k s)

/-- The rank of a symbol in the dependency hierarchy. -/
def Symbol.rank : ∀ {a s}, Symbol I sig a s → ℕ
  | _, _, .comp _ _ => 1
  | _, _, _ => 0

/-- Every symbol occurring in a composition domain has rank zero. -/
theorem domain_symbol_rank {a s} (σ : Symbol I sig a s)
    (τ : OperationSymbol (Symbol I sig))
    (h : τ ∈ EEquationSet.symbols ((epSignature I sig).domain σ)) :
    τ.2.2.rank < σ.rank := by
  cases σ with
  | base σ => obtain ⟨_, _, h, _⟩ := h; exact h.elim
  | source k s => obtain ⟨_, _, h, _⟩ := h; exact h.elim
  | target k s => obtain ⟨_, _, h, _⟩ := h; exact h.elim
  | comp k s =>
    obtain ⟨t, e, ⟨ht, he⟩, h⟩ := h
    cases ht
    cases he
    simp only [compositionDomain, boundary, Symbol.boundary, Bool.false_eq_true,
      ↓reduceIte, unary, EEquation.symbols, Term.symbols] at h
    rcases h with (rfl | ⟨j, h⟩) | (rfl | ⟨j, h⟩)
    · exact Nat.zero_lt_one
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      exact h.elim
    · exact Nat.zero_lt_one
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      exact h.elim

/-- The homogeneous categorial signature is hierarchical. -/
def hepSignature (I : Type i) {S : Type u} (sig : Signature.{u, v} S) : HepSignature S where
  toEPSignature := epSignature I sig
  wellFounded := Subrelation.wf (fun h => domain_symbol_rank _ _ h)
    (measure (fun p : OperationSymbol (Symbol I sig) => p.2.2.rank)).wf

/-- Interpret a categorial algebra as a partial algebra on its unchanged sorted carrier. -/
abbrev CategorialAlgebra.toPartialAlgebra [LT I] (A : CategorialAlgebra.{i, u, v, w} I sig) :
    PartialAlgebra (Symbol I sig) where
  carrier := A.carrier
  op
    | .base σ, z => Part.some ((A.op σ).toFun z)
    | .source k s, z => Part.some (((A.sort s).str.dim k).source (z 0))
    | .target k s, z => Part.some (((A.sort s).str.dim k).target (z 0))
    | .comp k s, z => ((A.sort s).str.dim k).comp (z 0) (z 1)

end Homogeneous
end CategorialAlgebras
