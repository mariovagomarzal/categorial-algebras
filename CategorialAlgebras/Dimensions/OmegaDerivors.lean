import CategorialAlgebras.Dimensions.HomogeneousComposition
import CategorialAlgebras.Dimensions.HeterogeneousComposition

/-!
# Dimension changes between finite dimensions and natural dimensions

Truncation includes dimensions, selecting the fixed points of the cutoff source
in the homogeneous presentation. Discretization retains the lower dimensions
and makes the remaining dimensions discrete.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

variable {S : Type u} (sig : Signature.{u, v} S)

/-- Inclusion of a finite initial segment into the natural dimensions. -/
def omegaInclusion (n : ℕ) : Fin n ↪o ℕ where
  toFun := Fin.val
  inj' := Fin.val_injective
  map_rel_iff' := Iff.rfl

/-- The minimum map from natural cell dimensions to the finite cutoff. -/
def omegaClamp (n : ℕ) : ℕ →o Fin (n + 1) where
  toFun k := ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  monotone' _ _ h := min_le_min_right _ h

/-- The minimum map retains each finite cell dimension below its cutoff. -/
@[simp] theorem omegaClamp_inclusion (n : ℕ) (k : Fin (n + 1)) :
    omegaClamp n k.val = k := by
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ k.isLt)

/-- The underlying homogeneous truncation includes every available dimension. -/
def homogeneousOmegaTruncationDerivor (n : ℕ) :
    Derivor (Homogeneous.Symbol (Fin n) sig) (Homogeneous.Symbol ℕ sig) :=
  homogeneousDimensionDerivor sig (fun k => some k.val)

/-- The equation requiring an element to be an $n$-cell. -/
def omegaTruncationEquation (n : ℕ) (s : S) :
    EEquation (Homogeneous.Symbol ℕ sig) (Word.Variables [s]) s :=
  ⟨.var (Word.position _ 0),
    Homogeneous.unary (.source n s) (.var (Word.position _ 0))⟩

/-- Homogeneous truncation from natural dimensions selects precisely the cutoff cells. -/
def homogeneousOmegaTruncation (n : ℕ) :
    GeneralizedHepDerivor (Homogeneous.hepSignature (Fin n) sig)
      (Homogeneous.hepSignature ℕ sig) where
  toDerivor := homogeneousOmegaTruncationDerivor sig n
  domain s := Homogeneous.singletonEquation (omegaTruncationEquation sig n s)

/-- The underlying homogeneous discretization retains dimensions below $n$. -/
def homogeneousOmegaDiscretizationDerivor (n : ℕ) :
    Derivor (Homogeneous.Symbol ℕ sig) (Homogeneous.Symbol (Fin n) sig) where
  sortMap := id
  image
    | .base σ => .app (.base σ) (fun j => .var (Word.position _ j))
    | .source k s => if h : k < n then
        Homogeneous.unary (.source ⟨k, h⟩ s) (.var (Word.position _ 0))
        else .var (Word.position _ 0)
    | .target k s => if h : k < n then
        Homogeneous.unary (.target ⟨k, h⟩ s) (.var (Word.position _ 0))
        else .var (Word.position _ 0)
    | .comp k _ => if h : k < n then
        Homogeneous.binary ⟨k, h⟩ (.var (Word.position _ 0))
          (.var (Word.position _ 1)) else .var (Word.position _ 0)

/-- Homogeneous discretization has empty cell domains. -/
def homogeneousOmegaDiscretization (n : ℕ) :
    GeneralizedHepDerivor (Homogeneous.hepSignature ℕ sig)
      (Homogeneous.hepSignature (Fin n) sig) where
  toDerivor := homogeneousOmegaDiscretizationDerivor sig n
  domain _ := ⊥

/-- Every underlying element is a discretization cell. -/
theorem homogeneousOmegaDiscretization_isCell (n : ℕ)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (s : S) (x : B.carrier s) : (homogeneousOmegaDiscretization sig n).IsCell B s x :=
  (homogeneousOmegaDiscretization sig n).isCell_of_empty (fun _ => rfl) B s x

/-- Heterogeneous truncation includes the finite cell dimensions. -/
def heterogeneousOmegaTruncation (n : ℕ) :
    GeneralizedHepDerivor (Heterogeneous.hepSignature (Fin (n + 1)) sig)
      (Heterogeneous.hepSignature ℕ sig) :=
  heterogeneousDimension sig (omegaInclusion (n + 1)).toOrderHom

/-- Heterogeneous discretization clamps every cell dimension at $n$. -/
def heterogeneousOmegaDiscretization (n : ℕ) :
    GeneralizedHepDerivor (Heterogeneous.hepSignature ℕ sig)
      (Heterogeneous.hepSignature (Fin (n + 1)) sig) :=
  heterogeneousDimension sig (omegaClamp n)

/-- Finite and natural heterogeneous truncations compose strictly, including domains. -/
theorem heterogeneousOmegaTruncation_comp {m n : ℕ} (h : m ≤ n) :
    (heterogeneousTruncation sig h).comp (heterogeneousOmegaTruncation sig n) =
      heterogeneousOmegaTruncation sig m := by
  unfold heterogeneousTruncation heterogeneousOmegaTruncation
  rw [heterogeneousDimension_compose]
  rfl

/-- Truncating an infinite discretization above its initial dimension discretizes. -/
theorem heterogeneousOmegaMixed_upper {m n : ℕ} (h : m ≤ n) :
    (heterogeneousOmegaTruncation sig n).comp (heterogeneousOmegaDiscretization sig m) =
      heterogeneousDiscretization sig h := by
  unfold heterogeneousOmegaTruncation heterogeneousOmegaDiscretization heterogeneousDiscretization
  rw [heterogeneousDimension_compose]
  rfl

/-- Truncating an infinite discretization below its initial dimension truncates. -/
theorem heterogeneousOmegaMixed_lower {m n : ℕ} (h : n ≤ m) :
    (heterogeneousOmegaTruncation sig n).comp (heterogeneousOmegaDiscretization sig m) =
      heterogeneousTruncation sig h := by
  unfold heterogeneousOmegaTruncation heterogeneousOmegaDiscretization heterogeneousTruncation
  rw [heterogeneousDimension_compose]
  congr 1
  ext k
  exact min_eq_left (le_trans (Nat.le_of_lt_succ k.isLt) h)

end CategorialAlgebras.Dimensions
