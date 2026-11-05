import CategorialAlgebras.Heterogeneous.Algebra
import CategorialAlgebras.HepDerivor.Signature
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# The heterogeneous categorial signature

Sorts are pairs of a dimension and an original sort. Original symbols have one copy in
each dimension. Only composition has a domain condition, involving source and target.
-/

universe i u v w x

namespace CategorialAlgebras.Heterogeneous

/-! ## Dimension words and families -/

/-- An input word with all its letters placed in dimension $k$. -/
abbrev dimensionWord {I : Type i} {S : Type u} (k : I) (a : List S) : List (I × S) :=
  a.map (fun s => (k, s))

/-- The letter at a position of a dimension word. -/
theorem dimensionWord_get {I : Type i} {S : Type u} (k : I) (a : List S)
    (j : Fin (dimensionWord k a).length) :
    (dimensionWord k a).get j = (k, a.get (Fin.cast (List.length_map _) j)) := by
  simp only [dimensionWord, List.get_eq_getElem, List.getElem_map, Fin.val_cast]

/-- Families on a dimension word are families of cells in that dimension. -/
def dimensionFamily {I : Type i} {S : Type u} {A : I × S → Type w} (k : I) (a : List S) :
    Word.Family A (dimensionWord k a) ≃ Word.Family (fun s => A (k, s)) a where
  toFun x j := by simpa only [List.get_eq_getElem, List.getElem_map, Fin.val_cast] using
    (x (Fin.cast (List.length_map (fun s => (k, s))).symm j))
  invFun x j := by simpa only [List.get_eq_getElem, List.getElem_map, Fin.val_cast] using
    (x (Fin.cast (List.length_map (fun s => (k, s))) j))
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

/-- Changing the carrier family commutes with dimensional reindexing. -/
theorem dimensionFamily_natural {I : Type i} {S : Type u}
    {A : I × S → Type w} {B : I × S → Type x} (f : SortedSet.Map A B)
    (k : I) (a : List S) (x : Word.Family A (dimensionWord k a)) :
    dimensionFamily k a (fun j => f _ (x j)) = fun j => f _ (dimensionFamily k a x j) := by
  funext j
  simp only [dimensionFamily, Equiv.coe_fn_mk]
  have transport (s t : I × S) (h : s = t) (z : A s) :
      cast (congrArg B h) (f s z) = f t (cast (congrArg A h) z) := by cases h; rfl
  exact transport _ _ (by simp [List.get_eq_getElem]) _

/-- Pointwise relations are preserved and reflected by dimensional reindexing. -/
theorem dimensionFamily_rel {I : Type i} {S : Type u}
    {A : I × S → Type w} {B : I × S → Type x}
    (R : ∀ s, A s → B s → Prop) (k : I) (a : List S)
    (x : Word.Family A (dimensionWord k a)) (y : Word.Family B (dimensionWord k a)) :
    (∀ j, R _ (x j) (y j)) ↔
      ∀ j, R _ (dimensionFamily k a x j) (dimensionFamily k a y j) := by
  have transport (s t : I × S) (h : s = t) (x : A s) (y : B s) :
      R s x y ↔ R t (cast (congrArg A h) x) (cast (congrArg B h) y) := by cases h; rfl
  constructor
  · intro h j
    simp only [dimensionFamily, Equiv.coe_fn_mk]
    exact (transport _ _ (by simp [List.get_eq_getElem]) _ _).mp (h _)
  · intro h j
    have hj := h (Fin.cast (List.length_map _) j)
    simp only [dimensionFamily, Equiv.coe_fn_mk] at hj
    exact (transport _ _ (by simp [List.get_eq_getElem]) _ _).mpr hj

/-! ## Symbols and terms -/

/-- The enlarged signature, with disjoint constructors for the symbol families. -/
inductive Symbol (I : Type i) [Preorder I] {S : Type u} (sig : Signature.{u, v} S) :
    List (I × S) → I × S → Type (max i v u)
  /-- An original operation in a specified dimension. -/
  | base (k : I) {a s} : sig a s → Symbol I sig (dimensionWord k a) (k, s)
  /-- Source between two dimensions. -/
  | source {j k : I} (h : j < k) (s : S) : Symbol I sig [(k, s)] (j, s)
  /-- Target between two dimensions. -/
  | target {j k : I} (h : j < k) (s : S) : Symbol I sig [(k, s)] (j, s)
  /-- Identity between two dimensions. -/
  | identity {j k : I} (h : j < k) (s : S) : Symbol I sig [(j, s)] (k, s)
  /-- Composition in an increasing pair of dimensions. -/
  | comp {j k : I} (h : j < k) (s : S) : Symbol I sig [(k, s), (k, s)] (k, s)

variable {I : Type i} [Preorder I] {S : Type u} {sig : Signature.{u, v} S}

/-- Select source (`false`) or target (`true`). -/
def Symbol.boundary {j k : I} (h : j < k) (s : S) (b : Bool) :
    Symbol I sig [(k, s)] (j, s) := if b then .target h s else .source h s

/-- Apply a unary symbol between possibly different sorts. -/
def unary {X : I × S → Type x} {s t} (σ : Symbol I sig [s] t)
    (r : Term (Symbol I sig) X s) : Term (Symbol I sig) X t :=
  .app σ (Fin.cases r (fun j => Fin.elim0 j))

/-- Apply a composition symbol to two terms. -/
def binary {X : I × S → Type x} {j k : I} (h : j < k) {s}
    (t r : Term (Symbol I sig) X (k, s)) : Term (Symbol I sig) X (k, s) :=
  .app (.comp h s) (Fin.cases t (Fin.cases r (fun j => Fin.elim0 j)))

/-- Apply a source or target symbol. -/
def boundary {X : I × S → Type x} {j k : I} (h : j < k) (b : Bool) {s}
    (t : Term (Symbol I sig) X (k, s)) : Term (Symbol I sig) X (j, s) :=
  unary (.boundary h s b) t

/-- Apply an identity symbol. -/
def identityTerm {X : I × S → Type x} {j k : I} (h : j < k) {s}
    (t : Term (Symbol I sig) X (j, s)) : Term (Symbol I sig) X (k, s) :=
  unary (.identity h s) t

/-- Apply an original symbol using its original input positions. -/
def base {X : I × S → Type x} (k : I) {a s} (σ : sig a s)
    (t : Word.Family (fun s => Term (Symbol I sig) X (k, s)) a) :
    Term (Symbol I sig) X (k, s) := .app (.base k σ) ((dimensionFamily k a).symm t)

/-- A single existence equation, as a sorted set. -/
def singletonEquation {T : Type u} {σ : Signature.{u, v} T} {X : T → Type x} {s}
    (e : EEquation σ X s) : EEquationSet σ X :=
  fun t => {e' | ∃ h : s = t, e' = h ▸ e}

/-- The unique composition domain equation. -/
def compositionDomain {j k : I} (h : j < k) (s : S) :
    EEquation (Symbol I sig) (Word.Variables [(k, s), (k, s)]) (j, s) :=
  (boundary h false (.var (Word.position _ 0)), boundary h true (.var (Word.position _ 1)))

/-! ## Domain conditions and hierarchy -/

/-- Only compositions have nonempty domain conditions. -/
def epSignature (I : Type i) [Preorder I] {S : Type u} (sig : Signature.{u, v} S) :
    EPSignature (I × S) where
  symbol := Symbol I sig
  domain
    | .base _ _ => fun _ => ∅
    | .source _ _ => fun _ => ∅
    | .target _ _ => fun _ => ∅
    | .identity _ _ => fun _ => ∅
    | .comp h s => singletonEquation (compositionDomain h s)

/-- Height in the dependency hierarchy. -/
def Symbol.rank : ∀ {a s}, Symbol I sig a s → ℕ
  | _, _, .comp _ _ => 1
  | _, _, _ => 0

/-- Domain dependencies strictly decrease height. -/
theorem domain_symbol_rank {a s} (σ : Symbol I sig a s)
    (τ : OperationSymbol (Symbol I sig))
    (h : τ ∈ EEquationSet.symbols ((epSignature I sig).domain σ)) :
    τ.2.2.rank < σ.rank := by
  cases σ with
  | base k σ => obtain ⟨_, _, h, _⟩ := h; exact h.elim
  | source hk s => obtain ⟨_, _, h, _⟩ := h; exact h.elim
  | target hk s => obtain ⟨_, _, h, _⟩ := h; exact h.elim
  | identity hk s => obtain ⟨_, _, h, _⟩ := h; exact h.elim
  | comp hk s =>
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

/-- The heterogeneous categorial signature is hierarchical. -/
def hepSignature (I : Type i) [Preorder I] {S : Type u} (sig : Signature.{u, v} S) :
    HepSignature (I × S) where
  toEPSignature := epSignature I sig
  wellFounded := Subrelation.wf (fun h => domain_symbol_rank _ _ h)
    (measure (fun p : OperationSymbol (Symbol I sig) => p.2.2.rank)).wf

/-! ## Expansion of categorial algebras -/

/-- Expansion on the exact carrier of sort $(k,s)$. -/
abbrev CategorialAlgebra.toPartialAlgebra (A : CategorialAlgebra.{i, u, v, w} I sig) :
    PartialAlgebra (Symbol I sig) where
  carrier := A.carrier
  op
    | .base k σ, z => Part.some ((A.op σ).toFun k (dimensionFamily k _ z))
    | .source h s, z => Part.some (((A.sort s).str.dim _ _ h).source (z 0))
    | .target h s, z => Part.some (((A.sort s).str.dim _ _ h).target (z 0))
    | .identity h s, z => Part.some (((A.sort s).str.dim _ _ h).identity (z 0))
    | .comp h s, z => ((A.sort s).str.dim _ _ h).comp (z 0) (z 1)

end CategorialAlgebras.Heterogeneous
