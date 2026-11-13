import CategorialAlgebras.Heterogeneous.Signature
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Finite.Prod

/-!
# Contextual equations for heterogeneous categorial algebras

Each equation uses its own finite context. The schemas express totality, the exact
composition domain, categorical laws, compatibility between dimensions and functoriality.
-/

universe i u v w x

namespace CategorialAlgebras.Heterogeneous

variable {I : Type i} [Preorder I] {S : Type u} {sig : Signature.{u, v} S}

/-! ## Finite variable contexts -/

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

/-- The variable at a position in a uniform context. -/
def variableTerm (s : I × S) {m : ℕ} (j : Fin m) :
    Term (Symbol I sig) (UniformVariables s m) s := .var ⟨j, ⟨rfl⟩⟩

/-- The existence assertion that a term is defined. -/
def defined {X : I × S → Type x} {s} (t : Term (Symbol I sig) X s) :
    EEquation (Symbol I sig) X s := (t, t)

/-- An equation in an arbitrary finite sorted context. -/
def contextualEquation {X : I × S → Type x} (hX : Finite (Σ s, X s)) {p : List (I × S)} {s}
    (prem : Word.Family (EEquation (Symbol I sig) X) p)
    (concl : EEquation (Symbol I sig) X s) : ContextualQEEquation (Symbol I sig) :=
  ⟨X, hX, p, s, ⟨prem, concl⟩⟩

/-- An equation whose variables all have a single sort; outputs may have other sorts. -/
def uniformEquation (s : I × S) (m : ℕ) {p : List (I × S)} {t : I × S}
    (prem : Word.Family (EEquation (Symbol I sig) (UniformVariables s m)) p)
    (concl : EEquation (Symbol I sig) (UniformVariables s m) t) :
    ContextualQEEquation (Symbol I sig) :=
  contextualEquation (uniformVariables_finite s m) prem concl

/-- The doubled positional context used for preservation of composition. -/
def PairVariables (a : List S) (s : S) := Word.Variables a s × Bool

/-- The doubled positional context is finite. -/
theorem pairVariables_finite (a : List S) : Finite (Σ s, PairVariables a s) := by
  have : Finite (Σ s, Word.Variables a s) := wordVariables_finite a
  exact Finite.of_injective
    (fun z : Σ s, PairVariables a s => ((⟨z.1, z.2.1⟩ : Σ s, Word.Variables a s), z.2.2))
    (by rintro ⟨s, j, b⟩ ⟨t, k, c⟩ h; cases h; rfl)

/-! ## Axiom schemas -/

/-- The finite schemas of heterogeneous categorial equations. -/
inductive Axiom (I : Type i) [Preorder I] {S : Type u} (sig : Signature.{u, v} S)
  /-- Every copy of an original operation is total. -/
  | total (k : I) {a s} (σ : sig a s)
  /-- Both boundaries are total. -/
  | boundaryTotal {j k : I} (h : j < k) (s : S) (b : Bool)
  /-- Identities are total. -/
  | identityTotal {j k : I} (h : j < k) (s : S)
  /-- Each boundary retracts the identity. -/
  | retract {j k : I} (h : j < k) (s : S) (b : Bool)
  /-- Defined composition implies matching boundaries. -/
  | domainForward {j k : I} (h : j < k) (s : S)
  /-- Matching boundaries imply defined composition. -/
  | domainBackward {j k : I} (h : j < k) (s : S)
  /-- The boundaries of a composite are its outer boundaries. -/
  | compositeBoundary {j k : I} (h : j < k) (s : S) (b : Bool)
  /-- Identities on boundaries act as units. -/
  | unit {j k : I} (h : j < k) (s : S) (b : Bool)
  /-- Adjacent compositions associate. -/
  | assoc {j k : I} (h : j < k) (s : S)
  /-- Original operations preserve boundaries. -/
  | operationBoundary {a s} (σ : sig a s) {j k : I} (h : j < k) (b : Bool)
  /-- Original operations preserve identities. -/
  | operationIdentity {a s} (σ : sig a s) {j k : I} (h : j < k)
  /-- Original operations preserve defined composition. -/
  | operationComposition {a s} (σ : sig a s) {j k : I} (h : j < k)
  /-- Taking a lower boundary absorbs either higher boundary. -/
  | globular {h j k : I} (hj : h < j) (jk : j < k) (s : S) (b c : Bool)
  /-- Successive identities equal the direct identity. -/
  | identityIdentity {h j k : I} (hj : h < j) (jk : j < k) (s : S)
  /-- Higher boundaries preserve lower composition. -/
  | boundaryComposition {h j k : I} (hj : h < j) (jk : j < k) (s : S) (b : Bool)
  /-- Compositions satisfy interchange. -/
  | interchange {h j k : I} (hj : h < j) (jk : j < k) (s : S)
  /-- Identities preserve lower composition. -/
  | identityComposition {h j k : I} (hj : h < j) (jk : j < k) (s : S)

/-- The contextual equation associated with an axiom schema. -/
def Axiom.equation : Axiom I sig → ContextualQEEquation (Symbol I sig)
  | .total k (a := a) σ =>
    let a' := dimensionWord k a
    let t := Term.app (.base k σ) (fun p => .var (Word.position a' p))
    contextualEquation (p := []) (wordVariables_finite a') (fun p => Fin.elim0 p) (defined t)
  | .boundaryTotal (k := k) h s b =>
    uniformEquation (k, s) 1 (p := []) (fun p => Fin.elim0 p)
      (defined (boundary h b (variableTerm (k, s) 0)))
  | .identityTotal (j := j) h s =>
    uniformEquation (j, s) 1 (p := []) (fun p => Fin.elim0 p)
      (defined (identityTerm h (variableTerm (j, s) 0)))
  | .retract (j := j) h s b =>
    let x := variableTerm (j, s) (m := 1) 0
    uniformEquation (j, s) 1 (p := []) (fun p => Fin.elim0 p)
      (boundary h b (identityTerm h x), x)
  | .domainForward (k := k) h s =>
    let x := variableTerm (k, s) (m := 2) 0
    let y := variableTerm (k, s) (m := 2) 1
    uniformEquation (k, s) 2 (p := [(k, s)])
      (Fin.cases (defined (binary h x y)) (fun p => Fin.elim0 p))
      (boundary h false x, boundary h true y)
  | .domainBackward (j := j) (k := k) h s =>
    let x := variableTerm (k, s) (m := 2) 0
    let y := variableTerm (k, s) (m := 2) 1
    uniformEquation (k, s) 2 (p := [(j, s)])
      (Fin.cases (boundary h false x, boundary h true y) (fun p => Fin.elim0 p))
      (defined (binary h x y))
  | .compositeBoundary (k := k) h s b =>
    let x := variableTerm (k, s) (m := 2) 0
    let y := variableTerm (k, s) (m := 2) 1
    uniformEquation (k, s) 2 (p := [(k, s)])
      (Fin.cases (defined (binary h x y)) (fun p => Fin.elim0 p))
      (boundary h b (binary h x y), boundary h b (if b then x else y))
  | .unit (k := k) h s b =>
    let x := variableTerm (k, s) (m := 1) 0
    uniformEquation (k, s) 1 (p := []) (fun p => Fin.elim0 p)
      ((if b then binary h (identityTerm h (boundary h true x)) x
        else binary h x (identityTerm h (boundary h false x))), x)
  | .assoc (k := k) h s =>
    let x := variableTerm (k, s) (m := 3) 0
    let y := variableTerm (k, s) (m := 3) 1
    let z := variableTerm (k, s) (m := 3) 2
    uniformEquation (k, s) 3 (p := [(k, s), (k, s)])
      (Fin.cases (defined (binary h x y))
        (Fin.cases (defined (binary h y z)) (fun p => Fin.elim0 p)))
      (binary h (binary h x y) z, binary h x (binary h y z))
  | .operationBoundary (a := a) σ (j := j) (k := k) h b =>
    let a' := dimensionWord k a
    let x := dimensionFamily k a (fun p => Term.var (Word.position a' p))
    contextualEquation (p := []) (wordVariables_finite a') (fun p => Fin.elim0 p)
      (boundary h b (base k σ x), base j σ (fun p => boundary h b (x p)))
  | .operationIdentity (a := a) σ (j := j) (k := k) h =>
    let a' := dimensionWord j a
    let x := dimensionFamily j a (fun p => Term.var (Word.position a' p))
    contextualEquation (p := []) (wordVariables_finite a') (fun p => Fin.elim0 p)
      (identityTerm h (base j σ x), base k σ (fun p => identityTerm h (x p)))
  | .operationComposition (a := a) σ (k := k) h =>
    let a' := dimensionWord k a
    let x := dimensionFamily k a (fun p => Term.var (Word.position a' p, false))
    let y := dimensionFamily k a (fun p => Term.var (Word.position a' p, true))
    contextualEquation (p := dimensionWord k a) (pairVariables_finite a')
      ((dimensionFamily k a).symm (fun p => defined (binary h (x p) (y p))))
      (base k σ (fun p => binary h (x p) (y p)), binary h (base k σ x) (base k σ y))
  | .globular (k := k) hj jk s b c =>
    let x := variableTerm (k, s) (m := 1) 0
    uniformEquation (k, s) 1 (p := []) (fun p => Fin.elim0 p)
      (boundary hj b (boundary jk c x), boundary (lt_trans hj jk) b x)
  | .identityIdentity (h := h) hj jk s =>
    let x := variableTerm (h, s) (m := 1) 0
    uniformEquation (h, s) 1 (p := []) (fun p => Fin.elim0 p)
      (identityTerm jk (identityTerm hj x), identityTerm (lt_trans hj jk) x)
  | .boundaryComposition (k := k) hj jk s b =>
    let x := variableTerm (k, s) (m := 2) 0
    let y := variableTerm (k, s) (m := 2) 1
    uniformEquation (k, s) 2 (p := [(k, s)])
      (Fin.cases (defined (binary (lt_trans hj jk) x y)) (fun p => Fin.elim0 p))
      (boundary jk b (binary (lt_trans hj jk) x y), binary hj (boundary jk b x) (boundary jk b y))
  | .interchange (k := k) hj jk s =>
    let x := variableTerm (k, s) (m := 4) 0
    let y := variableTerm (k, s) (m := 4) 1
    let z := variableTerm (k, s) (m := 4) 2
    let t := variableTerm (k, s) (m := 4) 3
    let hk := lt_trans hj jk
    uniformEquation (k, s) 4 (p := [(k, s), (k, s), (k, s), (k, s)])
      (Fin.cases (defined (binary jk x y)) (Fin.cases (defined (binary jk z t))
        (Fin.cases (defined (binary hk x z))
          (Fin.cases (defined (binary hk y t)) (fun p => Fin.elim0 p)))))
      (binary hk (binary jk x y) (binary jk z t), binary jk (binary hk x z) (binary hk y t))
  | .identityComposition (j := j) hj jk s =>
    let x := variableTerm (j, s) (m := 2) 0
    let y := variableTerm (j, s) (m := 2) 1
    uniformEquation (j, s) 2 (p := [(j, s)])
      (Fin.cases (defined (binary hj x y)) (fun p => Fin.elim0 p))
      (identityTerm jk (binary hj x y),
        binary (lt_trans hj jk) (identityTerm jk x) (identityTerm jk y))

/-! ## Specification and satisfaction -/

/-- The heterogeneous categorial ep-specification in arbitrary dimensions. -/
def specification (I : Type i) [Preorder I] {S : Type u} (sig : Signature.{u, v} S) :
    EPSpecification (epSignature I sig) where
  equations := Set.range Axiom.equation

/-- Satisfaction of the equations alone, without assuming ep-algebra domains. -/
def SatisfiesEquations (A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)) : Prop :=
  ∀ e : Axiom I sig, QEEquation.Valid A e.equation.equation

/-- Products preserve satisfaction, including the empty product. -/
theorem satisfiesEquations_product {J : Type x}
    (A : J → PartialAlgebra.{max i u, max i v u, w} (Symbol I sig))
    (h : ∀ j, SatisfiesEquations (A j)) : SatisfiesEquations (PartialAlgebra.product A) :=
  fun e => QEEquation.valid_product A e.equation.equation (fun j => h j e)

end CategorialAlgebras.Heterogeneous
