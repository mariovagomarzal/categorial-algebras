import CategorialAlgebras.Limits.ProjectiveSystem

/-!
# Inverse transition coherence

The inverse identifications embed lower stages in upper stages. Their
composition is controlled by the same canonical truncation comparisons.
-/

universe u v
namespace CategorialAlgebras.Limits.ProjectiveSystem.Family
open CategoryTheory
variable {C : ℕ → Type u} [∀ n, Category.{v} (C n)] {T : ProjectiveSystem C}

/-- Inverse transitions compose through the canonical comparison of truncations. -/
theorem inverse_coherence (A : T.Family) {m n p : ℕ} (h : m ≤ n) (k : n ≤ p) :
    (A.transition h).inv ≫ (T.truncation h).map (A.transition k).inv ≫
      (T.composition h k).hom.app (A.obj p) = (A.transition (le_trans h k)).inv := by
  apply (cancel_mono (A.transition (le_trans h k)).hom).mp
  rw [Category.assoc, Category.assoc, ← A.coherence h k]
  simp

end CategorialAlgebras.Limits.ProjectiveSystem.Family
