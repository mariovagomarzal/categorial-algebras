import CategorialAlgebras.Dimensions.Indices
import CategorialAlgebras.Presentations.Graduation

/-!
# Homogeneous dimension derivors

Discretization retains operations below the cutoff and interprets higher
boundaries and compositions by the first variable. Truncation includes the
operations and selects fixed points of the source at the cutoff.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory

variable {S : Type u} (sig : Signature.{u, v} S)

/-- The underlying homogeneous discretization derivor, including equal dimensions. -/
def homogeneousDiscretizationDerivor (n m : ℕ) :
    Derivor (Homogeneous.Symbol (Fin n) sig) (Homogeneous.Symbol (Fin m) sig) where
  sortMap := id
  image
    | .base σ => .app (.base σ) (fun j => .var (Word.position _ j))
    | .source k s => if h : k.val < m then
        Homogeneous.unary (.source ⟨k.val, h⟩ s) (.var (Word.position _ 0))
        else .var (Word.position _ 0)
    | .target k s => if h : k.val < m then
        Homogeneous.unary (.target ⟨k.val, h⟩ s) (.var (Word.position _ 0))
        else .var (Word.position _ 0)
    | .comp k _ => if h : k.val < m then
        Homogeneous.binary ⟨k.val, h⟩ (.var (Word.position _ 0))
          (.var (Word.position _ 1)) else .var (Word.position _ 0)

/-- In its own dimension the underlying discretization is the identity derivor. -/
@[simp] theorem homogeneousDiscretizationDerivor_self (n : ℕ) :
    homogeneousDiscretizationDerivor sig n n =
      Derivor.identity (Homogeneous.Symbol (Fin n) sig) := by
  apply Derivor.ext (c := homogeneousDiscretizationDerivor sig n n)
    (d := Derivor.identity _) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base σ => rfl
  | source k s =>
    simp only [homogeneousDiscretizationDerivor, dite_eq_left k.isLt]
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.source k s))
    funext j
    fin_cases j
    rfl
  | target k s =>
    simp only [homogeneousDiscretizationDerivor, dite_eq_left k.isLt]
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.target k s))
    funext j
    fin_cases j
    rfl
  | comp k s =>
    simp only [homogeneousDiscretizationDerivor, dite_eq_left k.isLt]
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.comp k s))
    funext j
    fin_cases j <;> rfl

/-- Homogeneous discretization has empty cell domains; the equal case is the identity. -/
def homogeneousDiscretization {m n : ℕ} (_h : m ≤ n) :
    GeneralizedHepDerivor (Homogeneous.hepSignature (Fin n) sig)
      (Homogeneous.hepSignature (Fin m) sig) where
  toDerivor := homogeneousDiscretizationDerivor sig n m
  domain _ := ⊥

/-- Every homogeneous discretization domain is empty. -/
@[simp] theorem homogeneousDiscretization_domain {m n : ℕ} (h : m ≤ n) (s : S) :
    (homogeneousDiscretization sig h).domain s = ⊥ := rfl

/-- Discretization in equal dimensions is the identity generalized hep-derivor. -/
@[simp] theorem homogeneousDiscretization_self (n : ℕ) :
    homogeneousDiscretization sig (le_refl n) =
      GeneralizedHepDerivor.identity (Homogeneous.hepSignature (Fin n) sig) := by
  apply GeneralizedHepDerivor.ext (homogeneousDiscretizationDerivor_self sig n)
  rfl

/-- All underlying elements are homogeneous discretization cells. -/
theorem homogeneousDiscretization_isCell {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (s : S) (x : B.carrier s) : (homogeneousDiscretization sig h).IsCell B s x :=
  (homogeneousDiscretization sig h).isCell_of_empty (fun _ => rfl) B s x

/-- Homogeneous discretization on partial algebras is the induced transformation. -/
noncomputable def homogeneousDiscretizationPartialFunctor {m n : ℕ} (h : m ≤ n) :
    PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig) ⥤
      PartialAlgebra (Homogeneous.Symbol (Fin n) sig) :=
  (homogeneousDiscretization sig h).transformedFunctor

/-- The underlying truncation derivor includes all the available operation symbols. -/
def homogeneousTruncationDerivor {m n : ℕ} (h : m ≤ n) :
    Derivor (Homogeneous.Symbol (Fin m) sig) (Homogeneous.Symbol (Fin n) sig) where
  sortMap := id
  image
    | .base σ => .app (.base σ) (fun j => .var (Word.position _ j))
    | .source k s => Homogeneous.unary (.source (dimensionInclusion h k) s)
        (.var (Word.position _ 0))
    | .target k s => Homogeneous.unary (.target (dimensionInclusion h k) s)
        (.var (Word.position _ 0))
    | .comp k _ => Homogeneous.binary (dimensionInclusion h k)
        (.var (Word.position _ 0)) (.var (Word.position _ 1))

/-- The fixed-source equation used in a proper homogeneous truncation. -/
def truncationEquation {n : ℕ} (k : Fin n) (s : S) :
    EEquation (Homogeneous.Symbol (Fin n) sig) (Word.Variables [s]) s :=
  Presentations.graduationEquation n sig k s

/-- Homogeneous truncation selects the $m$-cells, with an empty domain for $m=n$. -/
def homogeneousTruncation {m n : ℕ} (h : m ≤ n) :
    GeneralizedHepDerivor (Homogeneous.hepSignature (Fin m) sig)
      (Homogeneous.hepSignature (Fin n) sig) where
  toDerivor := homogeneousTruncationDerivor sig h
  domain s := if hm : m < n then
    Homogeneous.singletonEquation (truncationEquation sig ⟨m, hm⟩ s) else ⊥

/-- The domain of a proper truncation is the fixed-source singleton. -/
@[simp] theorem homogeneousTruncation_domain_of_lt {m n : ℕ} (h : m < n) (s : S) :
    (homogeneousTruncation sig h.le).domain s =
      Homogeneous.singletonEquation (truncationEquation sig ⟨m, h⟩ s) := by
  simp only [homogeneousTruncation, dite_eq_left h]
  rfl

/-- Equal-dimensional truncation has no cell equations. -/
@[simp] theorem homogeneousTruncation_domain_self (n : ℕ) (s : S) :
    (homogeneousTruncation sig (le_refl n)).domain s = ⊥ := by
  simp only [homogeneousTruncation, lt_self_iff_false, dite_false]
  rfl

/-- The equal-dimensional underlying truncation is the identity derivor. -/
@[simp] theorem homogeneousTruncationDerivor_self (n : ℕ) :
    homogeneousTruncationDerivor sig (le_refl n) =
      Derivor.identity (Homogeneous.Symbol (Fin n) sig) := by
  apply Derivor.ext (c := homogeneousTruncationDerivor sig (le_refl n))
    (d := Derivor.identity _) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base σ => rfl
  | source k s =>
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.source k s))
    funext j
    fin_cases j
    rfl
  | target k s =>
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.target k s))
    funext j
    fin_cases j
    rfl
  | comp k s =>
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.comp k s))
    funext j
    fin_cases j <;> rfl

/-- Truncation in equal dimensions is the identity generalized hep-derivor. -/
@[simp] theorem homogeneousTruncation_self (n : ℕ) :
    homogeneousTruncation sig (le_refl n) =
      GeneralizedHepDerivor.identity (Homogeneous.hepSignature (Fin n) sig) := by
  apply GeneralizedHepDerivor.ext (homogeneousTruncationDerivor_self sig n)
  apply heq_of_eq
  funext s
  exact homogeneousTruncation_domain_self sig n s

/-- In an expansion, truncation selects precisely the finite cells at its cutoff. -/
theorem homogeneousTruncation_isCell_iff {m n : ℕ} (h : m ≤ n)
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) (s : S) (x : B.carrier s) :
    (homogeneousTruncation sig h).IsCell B.toPartialAlgebra s x ↔
      Presentations.IsFiniteCell (B.sort s).str (cellInclusion h (Fin.last m)) x := by
  exact Presentations.graduation_isCell_iff n sig B
    (cellInclusion h (Fin.last m)) s x

/-- Homogeneous truncation on partial algebras is the induced transformation. -/
noncomputable def homogeneousTruncationPartialFunctor {m n : ℕ} (h : m ≤ n) :
    PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig) ⥤
      PartialAlgebra (Homogeneous.Symbol (Fin m) sig) :=
  (homogeneousTruncation sig h).transformedFunctor

end CategorialAlgebras.Dimensions
