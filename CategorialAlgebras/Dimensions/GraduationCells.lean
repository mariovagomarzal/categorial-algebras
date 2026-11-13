import CategorialAlgebras.Dimensions.GraduationDerivors
import CategorialAlgebras.Dimensions.HomogeneousCells

/-!
# Cells in the graduation compatibility squares

The extra cutoff equation of truncation follows from the lower-cell equation.
Reflexive existence equations introduced by discretization hold for every
cell. The canonical composition comparisons are therefore invertible on models.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open Presentations

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} {sig : Signature.{u, v} S}

/-- In a model, graduation selects precisely the recovered finite-dimensional cells. -/
theorem graduation_isCell_iff_model {n : ℕ}
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B)
    (k : Fin (n + 1)) (s : S) (x : B.carrier s) :
    (graduation n sig).IsCell B (k, s) x ↔
      IsFiniteCell ((recoveredAlgebra B hB).sort s).str k x := by
  by_cases hk : k.val < n
  · change EEquationSet.Satisfies B _ (if hh : k.val < n then _ else _) ↔ _
    erw [dite_eq_left hk]
    exact (satisfies_truncationEquation_iff B hB ⟨k.val, hk⟩ s x).trans
      ⟨fun hx _ => hx, fun hx => hx hk⟩
  · change EEquationSet.Satisfies B _ (if hh : k.val < n then _ else _) ↔ _
    erw [dite_eq_right hk]
    exact ⟨fun _ hh => (hk hh).elim, fun _ _ _ he => he.elim⟩

/-- The two truncation-graduation composites select the same cells in every model. -/
theorem truncation_graduation_sameCells {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B)
    (k : Fin (m + 1)) (s : S) (x : B.carrier s) :
    ((heterogeneousTruncation sig h).comp (graduation n sig)).IsCell B (k, s) x ↔
      ((graduation m sig).comp (homogeneousTruncation sig h)).IsCell B (k, s) x := by
  change EEquationSet.Satisfies B _ _ ↔ EEquationSet.Satisfies B _ _
  rw [truncation_graduation_domain, graduation_truncation_domain]
  change (graduation n sig).IsCell B (cellInclusion h k, s) x ↔ _
  rw [graduation_isCell_iff_model B hB]
  constructor
  · intro hx t e he
    rcases he with he | he
    · have hm := isFiniteCell_mono ((recoveredAlgebra B hB).sort s).str (show cellInclusion h k ≤ cellInclusion h (Fin.last m)
        from Nat.le_of_lt_succ k.isLt) hx
      exact (homogeneousTruncation_isCell_iff_model h B hB s x).mpr hm t e he
    · by_cases hk : k.val < m
      · erw [dite_eq_left hk] at he
        exact (satisfies_truncationEquation_iff B hB (dimensionInclusion h ⟨k.val, hk⟩) s x).mpr
          (hx (lt_of_lt_of_le hk h)) t e he
      · erw [dite_eq_right hk] at he
        exact he.elim
  · intro hx hn
    by_cases hk : k.val < m
    · have he : EEquationSet.Satisfies B (Word.singletonValuation x)
          (Homogeneous.singletonEquation (truncationEquation sig
            (dimensionInclusion h ⟨k.val, hk⟩) s)) := by
        intro t e he
        apply hx t e
        right
        erw [dite_eq_left hk]
        exact he
      exact (satisfies_truncationEquation_iff B hB _ s x).mp he
    · have he : (homogeneousTruncation sig h).IsCell B s x := fun t e he => hx t e (Or.inl he)
      have hm := (homogeneousTruncation_isCell_iff_model h B hB s x).mp he
      have hk' : k.val = m := by omega
      have hmn : m < n := by change k.val < n at hn; omega
      have hlow : (⟨(cellInclusion h k).val, hn⟩ : Fin n) = ⟨m, hmn⟩ := Fin.ext hk'
      change ((recoveredAlgebra B hB).sort s).str.IsCell _ x
      rw [hlow]
      exact hm hmn

/-- The two discretization-graduation composites select the same cells in every partial algebra. -/
theorem discretization_graduation_sameCells {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (k : Fin (n + 1)) (s : S) (x : B.carrier s) :
    ((graduation n sig).comp (homogeneousDiscretization sig h)).IsCell B (k, s) x ↔
      ((heterogeneousDiscretization sig h).comp (graduation m sig)).IsCell B (k, s) x := by
  change EEquationSet.Satisfies B _ _ ↔ EEquationSet.Satisfies B _ _
  rw [graduation_discretization_domain, discretization_graduation_domain]
  by_cases hk : k.val < m
  · have hn : k.val < n := lt_of_lt_of_le hk h
    have hc : (clampDimension m k).val < m := by change min k.val m < m; omega
    erw [dite_eq_left hn, dite_eq_left hk]
    change _ ↔ EEquationSet.Satisfies B _ (if hh : (clampDimension m k).val < m then _ else _)
    erw [dite_eq_left hc]
    have he : (⟨(clampDimension m k).val, hc⟩ : Fin m) = ⟨k.val, hk⟩ := Fin.ext (min_eq_left hk.le)
    rw [he]
    rfl
  · have hc : clampDimension m k = Fin.last m := Fin.ext (min_eq_right (Nat.le_of_not_gt hk))
    rw [hc, graduation_domain_last]
    by_cases hn : k.val < n
    · erw [dite_eq_left hn, dite_eq_right hk]
      exact ⟨fun _ _ _ he => he.elim, fun _ => satisfies_reflexiveEquation B s x⟩
    · erw [dite_eq_right hn]

/-- Graduation after truncation has a surjective canonical composition comparison on models. -/
theorem graduation_truncation_comparison_surjective {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    ∀ p, Function.Surjective
      (((graduation m sig).comparison (homogeneousTruncation sig h) B).toMap p) := by
  apply ((graduation m sig).comparison_surjective_iff (homogeneousTruncation sig h) B).mpr
  rintro ⟨k, s⟩ x hx
  apply (graduation_isCell_iff_model _ (homogeneousTruncation_isModel sig h B hB) k s x).mpr
  intro hk
  change EEquationSet.Satisfies B _ ((homogeneousTruncationDerivor sig h).translateSingletonSet _
    (if hh : k.val < m then _ else _)) at hx
  erw [dite_eq_left hk, truncation_translate_equation] at hx
  apply Subtype.ext
  exact (truncation_boundary_val h B hB ⟨k.val, hk⟩ false s x).trans
    ((satisfies_truncationEquation_iff B hB _ s x.val).mp hx)

/-- Graduation after discretization has a surjective canonical composition comparison on models. -/
theorem graduation_discretization_comparison_surjective {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (hB : (Homogeneous.specification (Fin m) sig).IsModel B) :
    ∀ p, Function.Surjective
      (((graduation n sig).comparison (homogeneousDiscretization sig h) B).toMap p) := by
  apply ((graduation n sig).comparison_surjective_iff (homogeneousDiscretization sig h) B).mpr
  rintro ⟨k, s⟩ x hx
  apply (graduation_isCell_iff_model _ (homogeneousDiscretization_isModel sig h B hB) k s x).mpr
  intro hk
  apply Subtype.ext
  have hv := discretization_boundary_val h B hB ⟨k.val, hk⟩ false s x
  by_cases hm : k.val < m
  · change EEquationSet.Satisfies B _ ((homogeneousDiscretizationDerivor sig n m).translateSingletonSet _
      (if hh : k.val < n then _ else _)) at hx
    erw [dite_eq_left hk, discretization_translate_equation_of_lt sig h _ hm] at hx
    erw [dite_eq_left hm] at hv
    exact hv.trans ((satisfies_truncationEquation_iff B hB _ s x.val).mp hx)
  · erw [dite_eq_right hm] at hv
    exact hv

end CategorialAlgebras.Dimensions
