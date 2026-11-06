import CategorialAlgebras.Dimensions.GraduationDerivors
import CategorialAlgebras.Dimensions.OmegaComposition

/-!
# The derivors underlying compatible finite graduations

The underlying derivors agree. Their generalized domains retain the cutoff
equation, so proper changes of cutoff give distinct generalized hep-derivors
despite selecting the same cells on models.
-/

universe u v w
namespace CategorialAlgebras.Omega
open Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} (sig : Signature.{u, v} S)

/-- Finite graduation after $\omega$-dimensional truncation, as a generalized hep-derivor. -/
def graduationComposite (n : ℕ) :
    GeneralizedHepDerivor (Heterogeneous.hepSignature (Fin (n+1)) sig)
      (Homogeneous.hepSignature ℕ sig) :=
  (graduation n sig).comp (homogeneousOmegaTruncation sig n)

/-- Restricting a finite graduation composite has the same underlying derivor as the lower composite. -/
theorem graduation_compatibility_derivor {m n : ℕ} (h : m ≤ n) :
    ((heterogeneousTruncation sig h).comp (graduationComposite sig n)).toDerivor =
      (graduationComposite sig m).toDerivor := by
  change (heterogeneousTruncation sig h).toDerivor.comp
    ((graduation n sig).toDerivor.comp (homogeneousOmegaTruncation sig n).toDerivor) = _
  rw [← Derivor.comp_assoc]
  change (((heterogeneousTruncation sig h).comp (graduation n sig)).toDerivor).comp _ = _
  rw [truncation_graduation_derivor]
  change ((graduation m sig).toDerivor.comp (homogeneousTruncation sig h).toDerivor).comp _ = _
  rw [Derivor.comp_assoc, homogeneousOmegaTruncation_comp_derivor]
  rfl

/-- The composite domain retains the cutoff equation and, below it, the cell equation. -/
theorem graduationComposite_domain (n : ℕ) (k : Fin (n+1)) (s : S) :
    (graduationComposite sig n).domain (k,s) =
      Homogeneous.singletonEquation (omegaTruncationEquation sig n s) ⊔
        (if _hk : k.val < n then
          Homogeneous.singletonEquation (omegaTruncationEquation sig k.val s) else ⊥) := by
  change _ ⊔ (homogeneousOmegaTruncationDerivor sig n).translateSingletonSet s
    (if hk : k.val < n then _ else _) = _
  by_cases hk : k.val < n
  · erw [dite_eq_left hk, dite_eq_left hk]
    exact congrArg (fun E => Homogeneous.singletonEquation (omegaTruncationEquation sig n s) ⊔ E)
      (omegaTruncation_translate_equation sig n ⟨k.val, hk⟩ s)
  · erw [dite_eq_right hk, dite_eq_right hk, Derivor.translateSingletonSet_empty]
    rfl

/-- Restriction with empty domains adds no equations to the composite domain. -/
theorem graduationRestricted_domain {m n : ℕ} (h : m ≤ n) (k : Fin (m+1)) (s : S) :
    ((heterogeneousTruncation sig h).comp (graduationComposite sig n)).domain (k,s) =
      (graduationComposite sig n).domain (cellInclusion h k,s) := by
  change _ ⊔ (graduationComposite sig n).toDerivor.translateSingletonSet _ ⊥ = _
  rw [Derivor.translateSingletonSet_empty, sup_bot_eq]
  rfl

/-- $\omega$-dimensional fixed-source equations in distinct dimensions are distinct terms. -/
theorem omegaTruncationEquation_ne {j k : ℕ} (h : j ≠ k) (s : S) :
    omegaTruncationEquation sig j s ≠ omegaTruncationEquation sig k s := by
  intro he
  have he' := congrArg Prod.snd he
  have hj : (⟨[s], s, Homogeneous.Symbol.source j s⟩ : OperationSymbol
      (Homogeneous.Symbol ℕ sig)) ∈ (omegaTruncationEquation sig j s).2.symbols := Or.inl rfl
  rw [he'] at hj
  rcases hj with he | ⟨q, hq⟩
  · have hjk : j = k := by
      have he0 := Set.mem_singleton_iff.mp he
      cases he0
      rfl
    exact h hjk
  · fin_cases q
    exact hq.elim

/-- Proper restriction changes the generalized hep-derivor, even at lower cutoff zero. -/
theorem graduation_compatibility_ne [Nonempty S] {m n : ℕ} (h : m < n) :
    (heterogeneousTruncation sig h.le).comp (graduationComposite sig n) ≠
      graduationComposite sig m := by
  intro he
  obtain ⟨s⟩ := ‹Nonempty S›
  have hd := congrFun (congrFun (eq_of_heq (hepDomain_heq
    (c := (heterogeneousTruncation sig h.le).comp (graduationComposite sig n))
    (d := graduationComposite sig m) he)) (Fin.last m,s)) s
  rw [graduationRestricted_domain, graduationComposite_domain, graduationComposite_domain] at hd
  have hm : (cellInclusion h.le (Fin.last m)).val < n := h
  erw [dite_eq_left hm, dite_eq_right (Nat.lt_irrefl m), sup_bot_eq] at hd
  rw [show (cellInclusion h.le (Fin.last m)).val = m from rfl] at hd
  have hn : omegaTruncationEquation sig n s ∈
      (Homogeneous.singletonEquation (omegaTruncationEquation sig n s) ⊔
        Homogeneous.singletonEquation (omegaTruncationEquation sig m s)) s := Or.inl ⟨rfl,rfl⟩
  rw [hd] at hn
  exact omegaTruncationEquation_ne sig (ne_of_gt h) s hn.2

/-- In equal dimensions the generalized hep-derivors agree completely. -/
theorem graduation_compatibility_self (n : ℕ) :
    (heterogeneousTruncation sig (le_refl n)).comp (graduationComposite sig n) =
      graduationComposite sig n := by
  rw [heterogeneousTruncation_self, GeneralizedHepDerivor.identity_comp]

/-- Satisfaction of a union of equation sets is simultaneous satisfaction of each set. -/
theorem satisfies_union {R : Type*} {σ : Signature R} {X : R → Type*}
    (A : PartialAlgebra σ) (a : SortedSet.Map X A.carrier)
    (E F : EEquationSet σ X) :
    EEquationSet.Satisfies A a (E ⊔ F) ↔
      EEquationSet.Satisfies A a E ∧ EEquationSet.Satisfies A a F := by
  constructor
  · intro h
    exact ⟨fun s e he => h s e (Or.inl he), fun s e he => h s e (Or.inr he)⟩
  · rintro ⟨hE,hF⟩ s e (he | he)
    · exact hE s e he
    · exact hF s e he

/-- On an expanded algebra the composite selects exactly the cells of its sort dimension. -/
theorem graduationComposite_isCell (n : ℕ)
    (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    (k : Fin (n+1)) (s : S) (x : A.carrier s) :
    (graduationComposite sig n).IsCell A.toPartialAlgebra (k,s) x ↔ (A.sort s).str.IsCell k.val x := by
  change EEquationSet.Satisfies A.toPartialAlgebra (Word.singletonValuation x) _ ↔ _
  rw [graduationComposite_domain, satisfies_union]
  have hn := homogeneousOmegaTruncation_isCell_iff sig n A s x
  change EEquationSet.Satisfies A.toPartialAlgebra (Word.singletonValuation x)
    (Homogeneous.singletonEquation (omegaTruncationEquation sig n s)) ↔ _ at hn
  rw [hn]
  by_cases hk : k.val < n
  · erw [dite_eq_left hk]
    have hh := homogeneousOmegaTruncation_isCell_iff sig k.val A s x
    change EEquationSet.Satisfies A.toPartialAlgebra (Word.singletonValuation x)
      (Homogeneous.singletonEquation (omegaTruncationEquation sig k.val s)) ↔ _ at hh
    rw [hh]
    exact ⟨And.right, fun hx => ⟨(A.sort s).str.isCell_mono hk.le hx, hx⟩⟩
  · erw [dite_eq_right hk]
    have he : k.val = n := le_antisymm (Nat.le_of_lt_succ k.isLt) (Nat.le_of_not_gt hk)
    rw [he]
    exact ⟨And.left, fun hx => ⟨hx, fun _ _ h => h.elim⟩⟩

/-- The distinct generalized domains select the same cells in the original algebra. -/
theorem graduation_compatibility_sameCells {m n : ℕ} (h : m ≤ n)
    (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    (k : Fin (m+1)) (s : S) (x : A.carrier s) :
    ((heterogeneousTruncation sig h).comp (graduationComposite sig n)).IsCell
      A.toPartialAlgebra (k,s) x ↔ (graduationComposite sig m).IsCell A.toPartialAlgebra (k,s) x := by
  change EEquationSet.Satisfies A.toPartialAlgebra (Word.singletonValuation x) _ ↔ _
  rw [graduationRestricted_domain]
  exact (graduationComposite_isCell sig n A (cellInclusion h k) s x).trans
    (graduationComposite_isCell sig m A k s x).symm

end CategorialAlgebras.Omega
