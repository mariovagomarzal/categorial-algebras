import CategorialAlgebras.Dimensions.HomogeneousDomains
import CategorialAlgebras.Dimensions.HeterogeneousComposition

/-!
# Dimension changes and graduation derivors

Graduation commutes with dimension changes at the level of underlying derivors.
The generalized domains can differ: truncation adds a redundant upper-cell
condition, and discretization can retain a reflexive existence equation.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open Presentations

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} (sig : Signature.{u, v} S)

set_option backward.isDefEq.respectTransparency false in
/-- Truncation and graduation have equal composite underlying derivors. -/
theorem truncation_graduation_derivor {m n : ℕ} (h : m ≤ n) :
    ((heterogeneousTruncation sig h).comp (graduation n sig)).toDerivor =
      ((graduation m sig).comp (homogeneousTruncation sig h)).toDerivor := by
  apply Derivor.ext (c := ((heterogeneousTruncation sig h).comp (graduation n sig)).toDerivor)
    (d := ((graduation m sig).comp (homogeneousTruncation sig h)).toDerivor) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base k σ =>
    change Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.base σ) _ = _
    congr 1
    funext q
    simp [graduation, graduationDerivor, graduationBase, heterogeneousTruncation,
      heterogeneousDimension, heterogeneousDimensionDerivor, homogeneousTruncation,
      homogeneousTruncationDerivor, Term.eval, Word.valuation, Derivor.positionMap,
      dimensionSortMap, Word.position, Word.mappedVariable, List.get_eq_getElem]
    apply eq_of_heq
    erw [eqRec_heq_iff]
    exact positionalTerm_heq _ _ _ _ rfl
  | source hj s =>
    have hh : cellInclusion h _ < cellInclusion h _ := hj
    simp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousTruncation,
      heterogeneousDimension, heterogeneousDimensionDerivor]
    erw [dite_eq_left hh]
    change Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (.source (dimensionInclusion h (lowerDimension hj)) s) _ = _
    congr 1
    funext q
    fin_cases q
    rfl
  | target hj s =>
    have hh : cellInclusion h _ < cellInclusion h _ := hj
    simp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousTruncation,
      heterogeneousDimension, heterogeneousDimensionDerivor]
    erw [dite_eq_left hh]
    change Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (.target (dimensionInclusion h (lowerDimension hj)) s) _ = _
    congr 1
    funext q
    fin_cases q
    rfl
  | identity hj s =>
    have hh : cellInclusion h _ < cellInclusion h _ := hj
    simp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousTruncation,
      heterogeneousDimension, heterogeneousDimensionDerivor]
    erw [dite_eq_left hh]
    rfl
  | comp hj s =>
    have hh : cellInclusion h _ < cellInclusion h _ := hj
    simp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousTruncation,
      heterogeneousDimension, heterogeneousDimensionDerivor]
    erw [dite_eq_left hh]
    change Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (.comp (dimensionInclusion h (lowerDimension hj)) s) _ = _
    congr 1
    funext q
    fin_cases q <;> rfl

/-- The truncation-first graduation composite retains the graduation domain at the included sort. -/
theorem truncation_graduation_domain {m n : ℕ} (h : m ≤ n) (k : Fin (m + 1)) (s : S) :
    ((heterogeneousTruncation sig h).comp (graduation n sig)).domain (k, s) =
      (graduation n sig).domain (cellInclusion h k, s) := by
  change _ ⊔ (graduationDerivor n sig).translateSingletonSet _ ⊥ = _
  erw [Derivor.translateSingletonSet_empty]
  exact sup_bot_eq _

/-- Graduation followed by truncation retains both the cutoff and lower-cell conditions. -/
theorem graduation_truncation_domain {m n : ℕ} (h : m ≤ n) (k : Fin (m + 1)) (s : S) :
    ((graduation m sig).comp (homogeneousTruncation sig h)).domain (k, s) =
      (homogeneousTruncation sig h).domain s ⊔
        (if hk : k.val < m then
          Homogeneous.singletonEquation (truncationEquation sig
            (dimensionInclusion h ⟨k.val, hk⟩) s) else ⊥) := by
  change _ ⊔ (homogeneousTruncationDerivor sig h).translateSingletonSet _
    (if hk : k.val < m then _ else _) = _
  by_cases hk : k.val < m
  · erw [dite_eq_left hk, dite_eq_left hk, truncation_translate_equation]
    rfl
  · erw [dite_eq_right hk, dite_eq_right hk, Derivor.translateSingletonSet_empty]
    rfl

/-- In equal dimensions the two graduation-truncation composites are equal, including domains. -/
theorem truncation_graduation_self (n : ℕ) :
    (heterogeneousTruncation sig (le_refl n)).comp (graduation n sig) =
      (graduation n sig).comp (homogeneousTruncation sig (le_refl n)) := by
  rw [heterogeneousTruncation_self, homogeneousTruncation_self,
    GeneralizedHepDerivor.identity_comp, GeneralizedHepDerivor.comp_identity]

/-- Truncation to dimension zero commutes strictly with graduation, including domains. -/
theorem truncation_graduation_zero (n : ℕ) :
    (heterogeneousTruncation sig (Nat.zero_le n)).comp (graduation n sig) =
      (graduation 0 sig).comp (homogeneousTruncation sig (Nat.zero_le n)) := by
  apply GeneralizedHepDerivor.ext (truncation_graduation_derivor sig _)
  apply heq_of_eq
  funext p
  rcases p with ⟨k, s⟩
  have hk : k = Fin.last 0 := Fin.ext (by omega)
  subst k
  rw [truncation_graduation_domain, graduation_truncation_domain]
  change (if hn : 0 < n then _ else _) = _ ⊔ (if hk : 0 < 0 then _ else _)
  rw [dite_eq_right (Nat.lt_irrefl 0), sup_bot_eq]
  rfl

/-- Proper positive truncation and graduation are unequal as generalized hep-derivors. -/
theorem truncation_graduation_ne [Nonempty S] {m n : ℕ} (hm : 0 < m) (hn : m < n) :
    (heterogeneousTruncation sig hn.le).comp (graduation n sig) ≠
      (graduation m sig).comp (homogeneousTruncation sig hn.le) := by
  intro he
  obtain ⟨s⟩ := ‹Nonempty S›
  let k : Fin (m + 1) := ⟨0, by omega⟩
  have hd := congrFun (congrFun (eq_of_heq (hepDomain_heq
    (c := (heterogeneousTruncation sig hn.le).comp (graduation n sig))
    (d := (graduation m sig).comp (homogeneousTruncation sig hn.le)) he)) (k, s)) s
  rw [truncation_graduation_domain, graduation_truncation_domain,
    homogeneousTruncation_domain_of_lt sig hn] at hd
  have hk : k.val < m := hm
  dsimp only [graduation] at hd
  erw [dite_eq_left (lt_trans hm hn), dite_eq_left hk] at hd
  have heq : truncationEquation sig ⟨m, hn⟩ s ∈
      (Homogeneous.singletonEquation (truncationEquation sig ⟨m, hn⟩ s) ⊔
        Homogeneous.singletonEquation (truncationEquation sig
          (dimensionInclusion hn.le ⟨k.val, hk⟩) s)) s := Or.inl ⟨rfl, rfl⟩
  rw [← hd] at heq
  obtain ⟨hs, heq⟩ := heq
  have heq' : truncationEquation sig ⟨m, hn⟩ s = truncationEquation sig ⟨0, lt_trans hm hn⟩ s := by
    exact heq
  exact truncationEquation_ne sig (by intro e; have := congrArg Fin.val e; simp only at this; omega) s heq'

set_option backward.isDefEq.respectTransparency false in
/-- Discretization and graduation have equal composite underlying derivors. -/
theorem discretization_graduation_derivor {m n : ℕ} (h : m ≤ n) :
    ((graduation n sig).comp (homogeneousDiscretization sig h)).toDerivor =
      ((heterogeneousDiscretization sig h).comp (graduation m sig)).toDerivor := by
  apply Derivor.ext
    (c := ((graduation n sig).comp (homogeneousDiscretization sig h)).toDerivor)
    (d := ((heterogeneousDiscretization sig h).comp (graduation m sig)).toDerivor) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base k σ =>
    change Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.base σ) _ = _
    congr 1
    funext q
    simp [graduation, graduationDerivor, graduationBase, heterogeneousDiscretization,
      heterogeneousDimension, heterogeneousDimensionDerivor, homogeneousDiscretization,
      homogeneousDiscretizationDerivor, Term.eval, Word.valuation, Derivor.positionMap,
      dimensionSortMap, Word.position, Word.mappedVariable, List.get_eq_getElem]
    apply eq_of_heq
    apply HEq.symm
    erw [eqRec_heq_iff]
    exact positionalTerm_heq _ _ _ _ rfl
  | @source j k hj s =>
    have hc := clampDimension_lt (m := m) hj
    by_cases hjm : j.val < m
    · have hh := hc.mpr hjm
      dsimp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousDiscretization,
        heterogeneousDimension, heterogeneousDimensionDerivor]
      erw [dite_eq_left hh]
      change Term.substFamily _ (if hh : j.val < m then _ else _) = _
      erw [dite_eq_left hjm]
      have he : lowerDimension hh = (⟨j.val, hjm⟩ : Fin m) := Fin.ext (min_eq_left hjm.le)
      change Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.source ⟨j.val, hjm⟩ s) _ =
        Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.source (lowerDimension hh) s) _
      rw [he]
      congr 1
      funext q
      fin_cases q
      rfl
    · have hh := mt hc.mp hjm
      dsimp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousDiscretization,
        heterogeneousDimension, heterogeneousDimensionDerivor]
      erw [dite_eq_right hh]
      change Term.substFamily _ (if hh : j.val < m then _ else _) = _
      erw [dite_eq_right hjm]
      rfl
  | @target j k hj s =>
    have hc := clampDimension_lt (m := m) hj
    by_cases hjm : j.val < m
    · have hh := hc.mpr hjm
      dsimp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousDiscretization,
        heterogeneousDimension, heterogeneousDimensionDerivor]
      erw [dite_eq_left hh]
      change Term.substFamily _ (if hh : j.val < m then _ else _) = _
      erw [dite_eq_left hjm]
      have he : lowerDimension hh = (⟨j.val, hjm⟩ : Fin m) := Fin.ext (min_eq_left hjm.le)
      change Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.target ⟨j.val, hjm⟩ s) _ =
        Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.target (lowerDimension hh) s) _
      rw [he]
      congr 1
      funext q
      fin_cases q
      rfl
    · have hh := mt hc.mp hjm
      dsimp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousDiscretization,
        heterogeneousDimension, heterogeneousDimensionDerivor]
      erw [dite_eq_right hh]
      change Term.substFamily _ (if hh : j.val < m then _ else _) = _
      erw [dite_eq_right hjm]
      rfl
  | @identity j k hj s =>
    dsimp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousDiscretization,
      heterogeneousDimension, heterogeneousDimensionDerivor]
    split <;> rfl
  | @comp j k hj s =>
    have hc := clampDimension_lt (m := m) hj
    by_cases hjm : j.val < m
    · have hh := hc.mpr hjm
      dsimp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousDiscretization,
        heterogeneousDimension, heterogeneousDimensionDerivor]
      erw [dite_eq_left hh]
      change Term.substFamily _ (if hh : j.val < m then _ else _) = _
      erw [dite_eq_left hjm]
      have he : lowerDimension hh = (⟨j.val, hjm⟩ : Fin m) := Fin.ext (min_eq_left hjm.le)
      change Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.comp ⟨j.val, hjm⟩ s) _ =
        Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.comp (lowerDimension hh) s) _
      rw [he]
      congr 1
      funext q
      fin_cases q <;> rfl
    · have hh := mt hc.mp hjm
      dsimp only [GeneralizedHepDerivor.comp, Derivor.comp, heterogeneousDiscretization,
        heterogeneousDimension, heterogeneousDimensionDerivor]
      erw [dite_eq_right hh]
      change Term.substFamily _ (if hh : j.val < m then _ else _) = _
      erw [dite_eq_right hjm]
      rfl

/-- Discretizing a graduation domain gives a lower fixed-source equation, a reflexive
existence equation in a discarded dimension, or the empty top domain. -/
theorem graduation_discretization_domain {m n : ℕ} (h : m ≤ n)
    (k : Fin (n + 1)) (s : S) :
    ((graduation n sig).comp (homogeneousDiscretization sig h)).domain (k, s) =
      if _hk : k.val < n then
        if hm : k.val < m then
          Homogeneous.singletonEquation (truncationEquation sig ⟨k.val, hm⟩ s)
        else Homogeneous.singletonEquation (reflexiveEquation (n := m) sig s)
      else ⊥ := by
  change ⊥ ⊔ (homogeneousDiscretizationDerivor sig n m).translateSingletonSet _
    (if hk : k.val < n then _ else _) = _
  by_cases hk : k.val < n
  · erw [dite_eq_left hk, dite_eq_left hk, bot_sup_eq]
    by_cases hm : k.val < m
    · erw [dite_eq_left hm, discretization_translate_equation_of_lt sig h _ hm]
      rfl
    · erw [dite_eq_right hm, discretization_translate_equation_of_le sig h _ (Nat.le_of_not_gt hm)]
      rfl
  · erw [dite_eq_right hk, dite_eq_right hk, Derivor.translateSingletonSet_empty, bot_sup_eq]

/-- Discretization followed by graduation retains only the domain at the clamped dimension. -/
theorem discretization_graduation_domain {m n : ℕ} (h : m ≤ n)
    (k : Fin (n + 1)) (s : S) :
    ((heterogeneousDiscretization sig h).comp (graduation m sig)).domain (k, s) =
      (graduation m sig).domain (clampDimension m k, s) := by
  change _ ⊔ (graduationDerivor m sig).translateSingletonSet _ ⊥ = _
  erw [Derivor.translateSingletonSet_empty]
  exact sup_bot_eq _

/-- Equal-dimensional discretization and graduation commute as complete generalized derivors. -/
theorem discretization_graduation_self (n : ℕ) :
    (graduation n sig).comp (homogeneousDiscretization sig (le_refl n)) =
      (heterogeneousDiscretization sig (le_refl n)).comp (graduation n sig) := by
  rw [homogeneousDiscretization_self, heterogeneousDiscretization_self,
    GeneralizedHepDerivor.identity_comp, GeneralizedHepDerivor.comp_identity]

/-- A proper discretization and graduation give unequal generalized derivors when a sort exists. -/
theorem discretization_graduation_ne [Nonempty S] {m n : ℕ} (h : m < n) :
    (graduation n sig).comp (homogeneousDiscretization sig h.le) ≠
      (heterogeneousDiscretization sig h.le).comp (graduation m sig) := by
  intro he
  obtain ⟨s⟩ := ‹Nonempty S›
  let k : Fin (n + 1) := ⟨m, by omega⟩
  have hd := congrFun (congrFun (eq_of_heq (hepDomain_heq
    (c := (graduation n sig).comp (homogeneousDiscretization sig h.le))
    (d := (heterogeneousDiscretization sig h.le).comp (graduation m sig)) he)) (k, s)) s
  rw [graduation_discretization_domain, discretization_graduation_domain] at hd
  have hk : k.val < n := h
  have hm : ¬ k.val < m := lt_irrefl m
  have hc : clampDimension m k = Fin.last m := Fin.ext (min_self m)
  erw [dite_eq_left hk, dite_eq_right hm, hc, graduation_domain_last] at hd
  have heq : reflexiveEquation (n := m) sig s ∈
      Homogeneous.singletonEquation (reflexiveEquation (n := m) sig s) s := ⟨rfl, rfl⟩
  rw [hd] at heq
  exact heq.elim

/-- With a nonempty sort set, truncation commutes strictly with graduation precisely
at dimension zero or when the dimensions agree. -/
theorem truncation_graduation_eq_iff [Nonempty S] {m n : ℕ} (h : m ≤ n) :
    (heterogeneousTruncation sig h).comp (graduation n sig) =
      (graduation m sig).comp (homogeneousTruncation sig h) ↔ m = 0 ∨ m = n := by
  constructor
  · intro he
    by_cases hm : m = 0
    · exact Or.inl hm
    · right
      by_contra hn
      exact truncation_graduation_ne sig (Nat.pos_of_ne_zero hm) (lt_of_le_of_ne h hn) he
  · rintro (rfl | rfl)
    · exact truncation_graduation_zero sig n
    · exact truncation_graduation_self sig m

/-- With a nonempty sort set, discretization commutes strictly with graduation precisely
when the dimensions agree. -/
theorem discretization_graduation_eq_iff [Nonempty S] {m n : ℕ} (h : m ≤ n) :
    (graduation n sig).comp (homogeneousDiscretization sig h) =
      (heterogeneousDiscretization sig h).comp (graduation m sig) ↔ m = n := by
  constructor
  · intro he
    by_contra hn
    exact discretization_graduation_ne sig (lt_of_le_of_ne h hn) he
  · rintro rfl
    exact discretization_graduation_self sig m

end CategorialAlgebras.Dimensions
