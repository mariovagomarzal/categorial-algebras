import CategorialAlgebras.Presentations.Dimensions

/-!
# Maps between finite dimensions

Inclusions retain dimensions and clamping sends a cell dimension $k$ to
$\min(k,m)$. Composition dimensions use `Fin n`, while cell dimensions use
`Fin (n + 1)`.
-/

namespace CategorialAlgebras.Dimensions

/-- Equality of generalized hep-derivors gives heterogeneous equality of their
dependent domain families. -/
theorem hepDomain_heq {S T : Type*} {sig : HepSignature S} {tau : HepSignature T}
    {c d : GeneralizedHepDerivor sig tau} (h : c = d) : HEq c.domain d.domain := by
  cases h
  rfl

/-- Positional variables with the same position give the same term up to sort transport. -/
theorem positionalTerm_heq {S T : Type*} {sig : Signature T} (φ : S → T)
    (a : List S) {s t : T} (x : Word.MappedVariables φ a s)
    (y : Word.MappedVariables φ a t) (h : x.val = y.val) :
    HEq (Term.var (sig := sig) x) (Term.var (sig := sig) y) := by
  rcases x with ⟨p, hp⟩
  rcases y with ⟨q, hq⟩
  dsimp only at h
  cases h
  cases hp
  cases hq
  rfl

/-- Evaluation of a positional variable changes only its sort by equality transport. -/
theorem valuation_heq {S T : Type*} {φ : S → T} {a : List S} {A : T → Type*}
    (x : Word.Family (fun s => A (φ s)) a) {s} (p : Word.MappedVariables φ a s) :
    HEq (Word.valuation x s p) (x p.val) := eqRec_heq p.property _

/-- Inclusion of composition dimensions. -/
def dimensionInclusion {m n : ℕ} (h : m ≤ n) : Fin m ↪o Fin n where
  toFun k := ⟨k.val, lt_of_lt_of_le k.isLt h⟩
  inj' := fun _ _ e => Fin.ext (congrArg (fun k : Fin n => k.val) e)
  map_rel_iff' := Iff.rfl

/-- Inclusion of cell dimensions, retaining the top cell dimension of the source. -/
def cellInclusion {m n : ℕ} (h : m ≤ n) : Fin (m + 1) ↪o Fin (n + 1) :=
  dimensionInclusion (Nat.add_le_add_right h 1)

/-- Clamping a cell dimension to $\min(k,m)$. -/
def clampDimension (m : ℕ) {n : ℕ} : Fin (n + 1) →o Fin (m + 1) where
  toFun k := ⟨min k.val m, Nat.lt_succ_of_le (min_le_right _ _)⟩
  monotone' _ _ h := show min _ m ≤ min _ m from min_le_min_right _ h

/-- Clamping does not change a dimension already below the cutoff. -/
@[simp] theorem clampDimension_inclusion {m n : ℕ} (h : m ≤ n) (k : Fin (m + 1)) :
    clampDimension m (cellInclusion h k) = k := by
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ k.isLt)

/-- Successive clamping is clamping to the smaller cutoff. -/
@[simp] theorem clampDimension_clampDimension {m n p : ℕ} (h : m ≤ n)
    (k : Fin (p + 1)) :
    clampDimension m (clampDimension n k) = clampDimension m k := by
  apply Fin.ext
  exact (min_assoc _ _ _).trans (congrArg (min k.val) (min_eq_right h))

/-- Clamping in its own dimension is the identity. -/
@[simp] theorem clampDimension_self (n : ℕ) (k : Fin (n + 1)) :
    clampDimension n k = k := by
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ k.isLt)

/-- A strictly increasing pair remains strict after clamping precisely below the cutoff. -/
theorem clampDimension_lt {m n : ℕ} {j k : Fin (n + 1)} (h : j < k) :
    clampDimension m j < clampDimension m k ↔ j.val < m := by
  change min j.val m < min k.val m ↔ j.val < m
  omega

end CategorialAlgebras.Dimensions
