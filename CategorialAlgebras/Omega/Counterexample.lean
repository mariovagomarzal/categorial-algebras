import CategorialAlgebras.Omega.Equivalence

/-!
# Unification cannot select a single dimensional carrier

A two-element idempotent monoid can first appear above any prescribed
dimension. Every carrier up to that dimension is a singleton, whereas
unification has two cells. A generalized hep-derivor selects a subtype of
one carrier, so cannot realize unification, even up to objectwise isomorphism.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} (sig : Signature.{u, v} S)

namespace UnificationCounterexample

/-- The chain cutoff is zero through dimension $k$ and one above it. -/
def cutoff (k j : ℕ) : ULift.{w} (Fin 2) := ULift.up (if j ≤ k then 0 else 1)

/-- The two-element cutoffs are increasing. -/
theorem cutoff_mono (k : ℕ) : Monotone (cutoff.{w} k) := by
  intro i j h
  by_cases hi : i ≤ k
  · simp only [cutoff, ite_eq_left hi]
    exact Fin.zero_le _
  · have hj : ¬ j ≤ k := fun hj => hi (le_trans h hj)
    simp only [cutoff, ite_eq_right hi, ite_eq_right hj, le_refl]

/-- Two cells, with the second cell appearing first above dimension $k$. -/
abbrev higherCategory (k : ℕ) : Homogeneous.HigherCategory.{0, w} ℕ where
  carrier := ULift.{w} (Fin 2)
  str.dim j := Homogeneous.chainDimension (cutoff k j)
  str.compatible _ _ h := Homogeneous.chain_compatible (cutoff_mono k h.le)

/-- The least element is fixed by all sources. -/
theorem zero_isCell (k j : ℕ) :
    (higherCategory.{w} k).str.IsCell j (ULift.up 0) := min_eq_left (show (ULift.up 0 : ULift.{w} (Fin 2)) ≤ cutoff k j from Fin.zero_le _)

/-- Every cell is fixed in dimension $k+1$. -/
theorem finite (k : ℕ) (x : (higherCategory.{w} k).carrier) :
    (higherCategory k).str.IsCell (k+1) x := by
  change min x (cutoff k (k+1)) = x
  apply min_eq_left
  simp only [cutoff, ite_eq_right (Nat.not_succ_le_self k)]
  exact Fin.le_last x.down

/-- Every original operation is the constant higher functor at the identity element. -/
def constant (k : ℕ) (C : Homogeneous.HigherCategory.{0, w} ℕ) :
    Homogeneous.Functor C (higherCategory k) where
  toFun _ := ULift.up 0
  map_source j _ := (zero_isCell k j).symm
  map_target j _ := (zero_isCell k j).symm
  map_comp _ _ _ _ _ := ⟨rfl, max_self _⟩

/-- The two-element algebra with constant original operations. -/
abbrev algebra (k : ℕ) : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig :=
  ⟨{ sort _ := higherCategory k, op _ := constant k _ }, fun _ x => ⟨k+1, finite k x⟩⟩

/-- The graduated carrier at the cutoff has exactly one element. -/
theorem low_unique (k : ℕ) (s : S) (x y : GraduatedCell (algebra.{u, v, w} sig k).obj k s) : x = y := by
  apply Subtype.ext
  have hx := x.property
  have hy := y.property
  change min x.val (cutoff k k) = x.val at hx
  change min y.val (cutoff k k) = y.val at hy
  have h0 : cutoff.{w} k k = ULift.up 0 := by simp [cutoff]
  rw [h0, min_eq_right (show (ULift.up 0 : ULift.{w} (Fin 2)) ≤ x.val from Fin.zero_le _)] at hx
  rw [h0, min_eq_right (show (ULift.up 0 : ULift.{w} (Fin 2)) ≤ y.val from Fin.zero_le _)] at hy
  exact hx.symm.trans hy

end UnificationCounterexample

/-- For nonempty sorts, no generalized hep-derivor realizes unification on every algebra,
even if arbitrary objectwise isomorphisms of partial algebras are allowed.

**Formally stronger** than the informal statement. Informally, no generalized hep-derivor induces
the unification functor; here no generalized hep-derivor gives, at every algebra, even a transformed
algebra isomorphic to the unification. -/
theorem unification_not_induced [Nonempty S]
    (c : GeneralizedHepDerivor (Homogeneous.hepSignature ℕ sig)
      (Heterogeneous.hepSignature ℕ sig)) :
    ¬ ∀ B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig,
      Nonempty (c.transformed B.toPartialAlgebra ≅ (unifiedAlgebra B).toPartialAlgebra) := by
  intro hc
  let s := Classical.choice ‹Nonempty S›
  let k := (c.sortMap s).1
  let A := UnificationCounterexample.algebra.{u, v, w} sig k
  let B := graduatedAlgebra A.obj
  obtain ⟨e⟩ := hc B
  have hs : Subsingleton ((c.transformed B.toPartialAlgebra).carrier s) := by
    constructor
    intro x y
    apply Subtype.ext
    exact UnificationCounterexample.low_unique sig k (c.sortMap s).2 x.val y.val
  have hb := e.hom.bijective_of_isIso s
  let x : GraduatedCell A.obj (k+1) s := ⟨ULift.up 0, UnificationCounterexample.finite k _⟩
  let y : GraduatedCell A.obj (k+1) s := ⟨ULift.up 1, UnificationCounterexample.finite k _⟩
  obtain ⟨x', hx⟩ := hb.2 (cellIn B (k+1) s x)
  obtain ⟨y', hy⟩ := hb.2 (cellIn B (k+1) s y)
  have he : cellIn B (k+1) s x = cellIn B (k+1) s y :=
    hx.symm.trans ((congrArg (e.hom.toMap s) (hs.elim x' y')).trans hy)
  have hxy := congrArg (fun z : GraduatedCell A.obj (k+1) s => z.val.down.val)
    (cellIn_injective B (k+1) s he)
  exact Nat.zero_ne_one hxy

end CategorialAlgebras.Omega
