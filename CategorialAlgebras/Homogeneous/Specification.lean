import CategorialAlgebras.Homogeneous.Signature
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Finite.Prod

/-!
# Contextual equations for categorial algebras

Each equation has exactly its own variables. The equations assert totality, categorical
composition laws, globularity, interchange, and functoriality of the original operations.
The construction works for any ordered type of dimensions.
-/

universe i u v w x

namespace CategorialAlgebras
namespace Homogeneous

variable {I : Type i} [LT I] {S : Type u} {sig : Signature.{u, v} S}

/-- A finite context of $m$ variables all of one sort. -/
def UniformVariables (s : S) (m : ℕ) (t : S) := Fin m × PLift (s = t)

/-- The disjoint union of a uniform context is finite, regardless of the set of sorts. -/
theorem uniformVariables_finite (s : S) (m : ℕ) : Finite (Σ t, UniformVariables s m t) :=
  Finite.of_injective (fun z => z.2.1) (by
    rintro ⟨t, j, ⟨h⟩⟩ ⟨t', j', ⟨h'⟩⟩ hj
    dsimp at hj
    subst j'
    cases h
    cases h'
    rfl)

/-- The disjoint union of the positional variables of a word is finite. -/
theorem wordVariables_finite (a : List S) : Finite (Σ t, Word.Variables a t) :=
  Finite.of_injective (fun z => z.2.val) (by
    rintro ⟨t, j, h⟩ ⟨t', j', h'⟩ hj
    dsimp at hj
    subst j'
    cases h
    cases h'
    rfl)

/-- The variable with index $j$ in a uniform context. -/
def variableTerm (s : S) {m : ℕ} (j : Fin m) :
    Term (Symbol I sig) (UniformVariables s m) s := .var ⟨j, ⟨rfl⟩⟩

/-- An existence assertion that a term is defined. -/
def defined {X : S → Type x} {s} (t : Term (Symbol I sig) X s) :
    EEquation (Symbol I sig) X s := (t, t)

/-- A contextual equation with one-sort variables and premises. -/
def uniformEquation (s : S) (m p : ℕ)
    (prem : Fin p → EEquation (Symbol I sig) (UniformVariables s m) s)
    (concl : EEquation (Symbol I sig) (UniformVariables s m) s) :
    ContextualQEEquation (Symbol I sig) where
  vars := UniformVariables s m
  finite := uniformVariables_finite s m
  premises := List.replicate p s
  sort := s
  equation.premises j :=
    (show (List.replicate p s).get j = s by simp).symm ▸
      prem (Fin.cast (List.length_replicate ..) j)
  equation.conclusion := concl

/-- A contextual equation with an arbitrary finite context. -/
def contextualEquation {X : S → Type x} (hX : Finite (Σ s, X s)) {p : List S} {s}
    (prem : Word.Family (EEquation (Symbol I sig) X) p)
    (concl : EEquation (Symbol I sig) X s) : ContextualQEEquation (Symbol I sig) :=
  ⟨X, hX, p, s, ⟨prem, concl⟩⟩

/-- The finite schemas of the homogeneous categorial equations. -/
inductive Axiom (I : Type i) [LT I] {S : Type u} (sig : Signature.{u, v} S)
  /-- Original operations are total. -/
  | total {a s} (σ : sig a s)
  /-- Boundaries are total. -/
  | boundaryTotal (k : I) (s : S) (b : Bool)
  /-- Every boundary is fixed by both boundaries in its dimension. -/
  | retract (k : I) (s : S) (b c : Bool)
  /-- A defined composition has matching boundaries. -/
  | domainForward (k : I) (s : S)
  /-- Matching boundaries ensure a defined composition. -/
  | domainBackward (k : I) (s : S)
  /-- Boundaries of a composite are the outer boundaries. -/
  | compositeBoundary (k : I) (s : S) (b : Bool)
  /-- Sources and targets act as units. -/
  | unit (k : I) (s : S) (b : Bool)
  /-- Adjacent compositions associate. -/
  | assoc (k : I) (s : S)
  /-- Original operations preserve boundaries. -/
  | operationBoundary {a s} (σ : sig a s) (k : I) (b : Bool)
  /-- Original operations preserve defined compositions. -/
  | operationComposition {a s} (σ : sig a s) (k : I)
  /-- A higher boundary fixes the corresponding lower boundary. -/
  | higherLower (l k : I) (h : l < k) (s : S) (b : Bool)
  /-- Lower boundaries absorb both higher boundaries. -/
  | lowerHigher (l k : I) (h : l < k) (s : S) (b c : Bool)
  /-- Higher boundaries preserve lower compositions. -/
  | boundaryComposition (l k : I) (h : l < k) (s : S) (b : Bool)
  /-- The two ways of composing a rectangle agree. -/
  | interchange (l k : I) (h : l < k) (s : S)

/-- The doubled positional context used for preservation of composition. -/
def PairVariables (a : List S) (s : S) := Word.Variables a s × Bool

/-- The doubled positional context is finite. -/
theorem pairVariables_finite (a : List S) : Finite (Σ s, PairVariables a s) := by
  have : Finite (Σ s, Word.Variables a s) := wordVariables_finite a
  exact Finite.of_injective
    (fun z : Σ s, PairVariables a s => ((⟨z.1, z.2.1⟩ : Σ s, Word.Variables a s), z.2.2))
    (by rintro ⟨s, j, b⟩ ⟨t, k, c⟩ h; cases h; rfl)

/-- The actual contextual equation represented by an axiom schema. -/
def Axiom.equation : Axiom I sig → ContextualQEEquation (Symbol I sig)
  | .total (a := a) σ =>
    let t := Term.app (.base σ) (fun j => .var (Word.position a j))
    contextualEquation (p := []) (wordVariables_finite a) (fun j => Fin.elim0 j) (defined t)
  | .boundaryTotal k s b =>
    uniformEquation s 1 0 (fun j => Fin.elim0 j) (defined (boundary k b (variableTerm s 0)))
  | .retract k s b c =>
    let t := boundary k c (variableTerm s (m := 1) 0)
    uniformEquation s 1 0 (fun j => Fin.elim0 j) (boundary k b t, t)
  | .domainForward k s =>
    let x := variableTerm s (m := 2) 0
    let y := variableTerm s (m := 2) 1
    uniformEquation s 2 1 (fun _ => defined (binary k x y))
      (boundary k false x, boundary k true y)
  | .domainBackward k s =>
    let x := variableTerm s (m := 2) 0
    let y := variableTerm s (m := 2) 1
    uniformEquation s 2 1 (fun _ => (boundary k false x, boundary k true y))
      (defined (binary k x y))
  | .compositeBoundary k s b =>
    let x := variableTerm s (m := 2) 0
    let y := variableTerm s (m := 2) 1
    uniformEquation s 2 1 (fun _ => defined (binary k x y))
      (boundary k b (binary k x y), boundary k b (if b then x else y))
  | .unit k s b =>
    let x := variableTerm s (m := 1) 0
    uniformEquation s 1 0 (fun j => Fin.elim0 j)
      ((if b then binary k (boundary k true x) x else binary k x (boundary k false x)), x)
  | .assoc k s =>
    let x := variableTerm s (m := 3) 0
    let y := variableTerm s (m := 3) 1
    let z := variableTerm s (m := 3) 2
    uniformEquation s 3 2
      (Fin.cases (defined (binary k x y)) (Fin.cases (defined (binary k y z)) Fin.elim0))
      (binary k (binary k x y) z, binary k x (binary k y z))
  | .operationBoundary (a := a) σ k b =>
    let x : Word.Family (Term (Symbol I sig) (Word.Variables a)) a :=
      fun j => .var (Word.position a j)
    contextualEquation (p := []) (wordVariables_finite a) (fun j => Fin.elim0 j)
      (boundary k b (.app (.base σ) x), .app (.base σ) (fun j => boundary k b (x j)))
  | .operationComposition (a := a) σ k =>
    let x : Word.Family (Term (Symbol I sig) (PairVariables a)) a :=
      fun j => .var (Word.position a j, false)
    let y : Word.Family (Term (Symbol I sig) (PairVariables a)) a :=
      fun j => .var (Word.position a j, true)
    contextualEquation (pairVariables_finite a) (fun j => defined (binary k (x j) (y j)))
      (.app (.base σ) (fun j => binary k (x j) (y j)),
        binary k (.app (.base σ) x) (.app (.base σ) y))
  | .higherLower l k _ s b =>
    let x := variableTerm s (m := 1) 0
    uniformEquation s 1 0 (fun j => Fin.elim0 j)
      (boundary k b (boundary l b x), boundary l b x)
  | .lowerHigher l k _ s b c =>
    let x := variableTerm s (m := 1) 0
    uniformEquation s 1 0 (fun j => Fin.elim0 j)
      (boundary l b (boundary k c x), boundary l b x)
  | .boundaryComposition l k _ s b =>
    let x := variableTerm s (m := 2) 0
    let y := variableTerm s (m := 2) 1
    uniformEquation s 2 1 (fun _ => defined (binary l x y))
      (boundary k b (binary l x y), binary l (boundary k b x) (boundary k b y))
  | .interchange l k _ s =>
    let x := variableTerm s (m := 4) 0
    let y := variableTerm s (m := 4) 1
    let z := variableTerm s (m := 4) 2
    let t := variableTerm s (m := 4) 3
    uniformEquation s 4 4
      (Fin.cases (defined (binary l x y))
        (Fin.cases (defined (binary l z t))
          (Fin.cases (defined (binary k x z)) (Fin.cases (defined (binary k y t)) Fin.elim0))))
      (binary k (binary l x y) (binary l z t), binary l (binary k x z) (binary k y t))

/-- The homogeneous categorial ep-specification in arbitrary dimensions. -/
def specification (I : Type i) [LT I] {S : Type u} (sig : Signature.{u, v} S) :
    EPSpecification (epSignature I sig) where
  equations := Set.range Axiom.equation

/-- Satisfaction of the contextual equations alone, without assuming ep-algebra domains. -/
def SatisfiesEquations (A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)) : Prop :=
  ∀ e : Axiom I sig, QEEquation.Valid A e.equation.equation

/-- Satisfaction of contextual equations is closed under arbitrary products. -/
theorem satisfiesEquations_product {J : Type x}
    (A : J → PartialAlgebra.{u, max i v u, w} (Symbol I sig))
    (h : ∀ j, SatisfiesEquations (A j)) : SatisfiesEquations (PartialAlgebra.product A) :=
  fun e => QEEquation.valid_product A e.equation.equation (fun j => h j e)

end Homogeneous
end CategorialAlgebras
