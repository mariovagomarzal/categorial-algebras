import CategorialAlgebras.Dimensions.HeterogeneousComposition
import CategorialAlgebras.Dimensions.HomogeneousDerivors
import CategorialAlgebras.Presentations.Unification

/-!
# Discretization and unification derivors

Clamping the top dimension gives the top dimension of the smaller algebra.
Unification and discretization therefore commute as complete generalized
hep-derivors, including their empty cell domains.
-/

universe u v

namespace CategorialAlgebras.Dimensions

open Presentations

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} (sig : Signature.{u, v} S)

/-- Clamping the uppermost dimension gives the uppermost retained dimension. -/
@[simp] theorem clampDimension_last {m n : ℕ} (h : m ≤ n) :
    clampDimension m (Fin.last n) = Fin.last m := Fin.ext (min_eq_right h)

/-- Pointwise heterogeneous equality of images suffices to compare derivors. -/
theorem derivor_ext_heq {S T : Type*} {σ : Signature S} {τ : Signature T}
    {c d : Derivor σ τ} (h : c.sortMap = d.sortMap)
    (hi : ∀ a s (f : σ a s), HEq (c.image f) (d.image f)) : c = d := by
  rcases c with ⟨c, ci⟩
  rcases d with ⟨d, di⟩
  cases h
  apply Derivor.ext (c := ⟨c, ci⟩) (d := ⟨c, di⟩) rfl
  apply heq_of_eq
  funext a s f
  exact eq_of_heq (hi a s f)

/-- A base-operation term in an arbitrary selected cell dimension. -/
def selectedBase {m : ℕ} (k : Fin (m + 1)) {a s} (σ : sig a s) :
    Term (Heterogeneous.Symbol (Fin (m + 1)) sig)
      (Word.MappedVariables (fun s => (k, s)) a) (k, s) :=
  .app (.base k σ) (fun q => .var ⟨Fin.cast (List.length_map _) q, by
    simp [Heterogeneous.dimensionWord, List.get_eq_getElem]⟩)

/-- A homogeneous boundary encoded between a selected top and a lower dimension. -/
def selectedBoundary {m : ℕ} {j k : Fin (m + 1)} (h : j < k) (s : S) (b : Bool) :
    Term (Heterogeneous.Symbol (Fin (m + 1)) sig)
      (Word.MappedVariables (fun s => (k, s)) [s]) (k, s) :=
  Heterogeneous.identityTerm h (Heterogeneous.boundary h b
    (.var (Word.mappedVariable (fun s => (k, s)) _ 0)))

/-- A homogeneous composition encoded on a selected top carrier. -/
def selectedComp {m : ℕ} {j k : Fin (m + 1)} (h : j < k) (s : S) :
    Term (Heterogeneous.Symbol (Fin (m + 1)) sig)
      (Word.MappedVariables (fun s => (k, s)) [s, s]) (k, s) :=
  Heterogeneous.binary h (.var (Word.mappedVariable (fun s => (k, s)) _ 0))
    (.var (Word.mappedVariable (fun s => (k, s)) _ 1))

/-- Encoded compositions respect equality of both dimensions. -/
theorem selectedComp_heq {m : ℕ} {j k j' k' : Fin (m + 1)}
    (h : j < k) (h' : j' < k') (hj : j = j') (hk : k = k') (s : S) :
    HEq (selectedComp sig h s) (selectedComp sig h' s) := by
  cases hj
  cases hk
  rfl

/-- Encoded homogeneous boundaries respect equality of both dimensions. -/
theorem selectedBoundary_heq {m : ℕ} {j k j' k' : Fin (m + 1)}
    (h : j < k) (h' : j' < k') (hj : j = j') (hk : k = k') (s : S) (b : Bool) :
    HEq (selectedBoundary sig h s b) (selectedBoundary sig h' s b) := by
  cases hj
  cases hk
  rfl

/-- Evaluation at equal indices gives heterogeneous equality for any dependent family. -/
theorem dependent_heq {A : Sort*} {B : A → Sort*} (f : ∀ a, B a) {a b : A} (h : a = b) :
    HEq (f a) (f b) := by cases h; rfl

/-- Equal sort maps and positions give heterogeneous equality of positional terms. -/
theorem positionalTerm_maps_heq {A B : Type*} {τ : Signature B} (φ ψ : A → B)
    (h : φ = ψ) (a : List A) {s t : B} (x : Word.MappedVariables φ a s)
    (y : Word.MappedVariables ψ a t) (hp : x.val = y.val) :
    HEq (Term.var (sig := τ) x) (Term.var (sig := τ) y) := by
  cases h
  exact positionalTerm_heq φ a x y hp

/-- Discretization and unification have equal composite underlying derivors. -/
theorem discretization_unification_derivor {m n : ℕ} (h : m ≤ n) :
    ((unification n sig).comp (heterogeneousDiscretization sig h)).toDerivor =
      ((homogeneousDiscretization sig h).comp (unification m sig)).toDerivor := by
  apply derivor_ext_heq
  · funext s
    exact Prod.ext (clampDimension_last h) rfl
  intro a s σ
  cases σ with
  | base σ =>
    have hl : ((unification n sig).comp (heterogeneousDiscretization sig h)).image (.base σ) =
        selectedBase sig (clampDimension m (Fin.last n)) σ := by
      change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig)
        (.base (clampDimension m (Fin.last n)) σ) _ = _
      apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig)
        (.base (clampDimension m (Fin.last n)) σ))
      funext q
      simp [heterogeneousDiscretization, heterogeneousDimension, heterogeneousDimensionDerivor,
        unification, unificationDerivor, Term.eval, Word.valuation,
        Derivor.positionMap, dimensionSortMap, Word.mappedVariable, List.get_eq_getElem]
      apply eq_of_heq
      erw [eqRec_heq_iff]
      exact positionalTerm_heq _ _ _ _ rfl
    have hr : ((homogeneousDiscretization sig h).comp (unification m sig)).image (.base σ) =
        selectedBase sig (Fin.last m) σ := by
      change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.base (Fin.last m) σ) _ = _
      apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.base (Fin.last m) σ))
      funext q
      simp [homogeneousDiscretization, homogeneousDiscretizationDerivor, unification,
        unificationDerivor, Term.eval, Word.valuation, Derivor.positionMap,
        Word.position, Word.mappedVariable, List.get_eq_getElem]
      apply eq_of_heq
      erw [eqRec_heq_iff]
      exact positionalTerm_heq _ _ _ _ rfl
    exact (heq_of_eq hl).trans ((dependent_heq (fun k => selectedBase sig k σ)
      (clampDimension_last h)).trans (heq_of_eq hr.symm))
  | source k s =>
    have hc := clampDimension_lt (m := m) (castSucc_lt_last k)
    by_cases hk : k.val < m
    · have hh := hc.mpr hk
      have hl : ((unification n sig).comp (heterogeneousDiscretization sig h)).image (.source k s) =
          selectedBoundary sig hh s false := by
        change Term.substFamily _ (if hp : _ then _ else _) = _
        erw [dite_eq_left hh]
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.identity hh s) _ = _
        apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.identity hh s))
        funext q
        fin_cases q
        change Term.substFamily _ (if hp : _ then _ else _) = _
        erw [dite_eq_left hh]
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.source hh s) _ = _
        congr 1
        funext q
        fin_cases q
        rfl
      have hr : ((homogeneousDiscretization sig h).comp (unification m sig)).image (.source k s) =
          selectedBoundary sig (castSucc_lt_last (⟨k.val, hk⟩ : Fin m)) s false := by
        change (unificationDerivor m sig).translate _ (if hp : _ then _ else _) = _
        erw [dite_eq_left hk]
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig)
          (.identity (castSucc_lt_last (⟨k.val, hk⟩ : Fin m)) s) _ = _
        congr 1
        funext q
        fin_cases q
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig)
          (.source (castSucc_lt_last (⟨k.val, hk⟩ : Fin m)) s) _ = _
        congr 1
        funext q
        fin_cases q
        rfl
      exact (heq_of_eq hl).trans ((selectedBoundary_heq sig hh (castSucc_lt_last (⟨k.val, hk⟩ : Fin m))
        (Fin.ext (min_eq_left hk.le)) (clampDimension_last h) s false).trans (heq_of_eq hr.symm))
    · have hh := mt hc.mp hk
      simp only [GeneralizedHepDerivor.comp, Derivor.comp, unification, unificationDerivor,
        heterogeneousDiscretization, heterogeneousDimension, homogeneousDiscretization,
        homogeneousDiscretizationDerivor]
      simp only [Heterogeneous.identityTerm, Heterogeneous.boundary, Heterogeneous.Symbol.boundary,
        Bool.false_eq_true, ite_false, Heterogeneous.unary, Derivor.translate_app,
        heterogeneousDimensionDerivor_identity,
        dite_eq_right hh, dite_eq_right hk, Term.substFamily, Term.subst_var]
      simp only [Derivor.translate_var]
      simp only [Word.valuation, Derivor.positionMap, Word.position, Word.mappedVariable]
      simp only [eqRec_heq_iff]
      change HEq (Term.substFamily _ (if hp : _ then _ else _)) (Term.var _)
      erw [dite_eq_right hh]
      simp only [Term.substFamily]
      simp only [Term.subst_var, Word.valuation, Term.eval, Derivor.positionMap,
        Fin.cases_zero]
      simp only [eqRec_heq_iff]
      exact positionalTerm_maps_heq (fun s => (clampDimension m (Fin.last n), s))
        (fun s => (Fin.last m, s)) (funext (fun s => Prod.ext (clampDimension_last h) rfl)) _ _ _ rfl
  | target k s =>
    have hc := clampDimension_lt (m := m) (castSucc_lt_last k)
    by_cases hk : k.val < m
    · have hh := hc.mpr hk
      have hl : ((unification n sig).comp (heterogeneousDiscretization sig h)).image (.target k s) =
          selectedBoundary sig hh s true := by
        change Term.substFamily _ (if hp : _ then _ else _) = _
        erw [dite_eq_left hh]
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.identity hh s) _ = _
        apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.identity hh s))
        funext q
        fin_cases q
        change Term.substFamily _ (if hp : _ then _ else _) = _
        erw [dite_eq_left hh]
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.target hh s) _ = _
        congr 1
        funext q
        fin_cases q
        rfl
      have hr : ((homogeneousDiscretization sig h).comp (unification m sig)).image (.target k s) =
          selectedBoundary sig (castSucc_lt_last (⟨k.val, hk⟩ : Fin m)) s true := by
        change (unificationDerivor m sig).translate _ (if hp : _ then _ else _) = _
        erw [dite_eq_left hk]
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig)
          (.identity (castSucc_lt_last (⟨k.val, hk⟩ : Fin m)) s) _ = _
        congr 1
        funext q
        fin_cases q
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig)
          (.target (castSucc_lt_last (⟨k.val, hk⟩ : Fin m)) s) _ = _
        congr 1
        funext q
        fin_cases q
        rfl
      exact (heq_of_eq hl).trans ((selectedBoundary_heq sig hh (castSucc_lt_last (⟨k.val, hk⟩ : Fin m))
        (Fin.ext (min_eq_left hk.le)) (clampDimension_last h) s true).trans (heq_of_eq hr.symm))
    · have hh := mt hc.mp hk
      simp only [GeneralizedHepDerivor.comp, Derivor.comp, unification, unificationDerivor,
        heterogeneousDiscretization, heterogeneousDimension, homogeneousDiscretization,
        homogeneousDiscretizationDerivor]
      simp only [Heterogeneous.identityTerm, Heterogeneous.boundary, Heterogeneous.Symbol.boundary,
        ite_true, Heterogeneous.unary, Derivor.translate_app,
        heterogeneousDimensionDerivor_identity,
        dite_eq_right hh, dite_eq_right hk, Term.substFamily, Term.subst_var]
      simp only [Derivor.translate_var]
      simp only [Word.valuation, Derivor.positionMap, Word.position, Word.mappedVariable]
      simp only [eqRec_heq_iff]
      change HEq (Term.substFamily _ (if hp : _ then _ else _)) (Term.var _)
      erw [dite_eq_right hh]
      simp only [Term.substFamily]
      simp only [Term.subst_var, Word.valuation, Term.eval, Derivor.positionMap,
        Fin.cases_zero]
      simp only [eqRec_heq_iff]
      exact positionalTerm_maps_heq (fun s => (clampDimension m (Fin.last n), s))
        (fun s => (Fin.last m, s)) (funext (fun s => Prod.ext (clampDimension_last h) rfl)) _ _ _ rfl
  | comp k s =>
    have hc := clampDimension_lt (m := m) (castSucc_lt_last k)
    by_cases hk : k.val < m
    · have hh := hc.mpr hk
      have hl : ((unification n sig).comp (heterogeneousDiscretization sig h)).image (.comp k s) =
          selectedComp sig hh s := by
        change Term.substFamily _ (if hp : _ then _ else _) = _
        erw [dite_eq_left hh]
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig) (.comp hh s) _ = _
        congr 1
        funext q
        fin_cases q <;> rfl
      have hr : ((homogeneousDiscretization sig h).comp (unification m sig)).image (.comp k s) =
          selectedComp sig (castSucc_lt_last (⟨k.val, hk⟩ : Fin m)) s := by
        change (unificationDerivor m sig).translate _ (if hp : _ then _ else _) = _
        erw [dite_eq_left hk]
        change Term.app (sig := Heterogeneous.Symbol (Fin (m + 1)) sig)
          (.comp (castSucc_lt_last (⟨k.val, hk⟩ : Fin m)) s) _ = _
        congr 1
        funext q
        fin_cases q <;> rfl
      exact (heq_of_eq hl).trans ((selectedComp_heq sig hh (castSucc_lt_last (⟨k.val, hk⟩ : Fin m))
        (Fin.ext (min_eq_left hk.le)) (clampDimension_last h) s).trans (heq_of_eq hr.symm))
    · have hh := mt hc.mp hk
      change HEq (Term.substFamily _ (if hp : _ then _ else _))
        ((unificationDerivor m sig).translate _ (if hp : _ then _ else _))
      erw [dite_eq_right hh, dite_eq_right hk]
      exact positionalTerm_maps_heq (fun s => (clampDimension m (Fin.last n), s))
        (fun s => (Fin.last m, s)) (funext (fun s => Prod.ext (clampDimension_last h) rfl)) _ _ _ rfl

/-- Empty-domain generalized derivors are equal when their underlying derivors are equal. -/
theorem hep_ext_empty {A B : Type*} {σ : HepSignature A} {τ : HepSignature B}
    {c d : GeneralizedHepDerivor σ τ} (h : c.toDerivor = d.toDerivor)
    (hc : ∀ s, c.domain s = ⊥) (hd : ∀ s, d.domain s = ⊥) : c = d := by
  rcases c with ⟨c, C⟩
  rcases d with ⟨d, D⟩
  change c = d at h
  cases h
  apply GeneralizedHepDerivor.ext (c := ⟨c, C⟩) (d := ⟨c, D⟩) rfl
  apply heq_of_eq
  exact (funext hc).trans (funext hd).symm

/-- Discretization and unification commute as complete generalized hep-derivors. -/
theorem discretization_unification {m n : ℕ} (h : m ≤ n) :
    (unification n sig).comp (heterogeneousDiscretization sig h) =
      (homogeneousDiscretization sig h).comp (unification m sig) := by
  apply hep_ext_empty (discretization_unification_derivor sig h)
  · intro s
    change ⊥ ⊔ (heterogeneousDimensionDerivor sig (clampDimension m)).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]
  · intro s
    change ⊥ ⊔ (unificationDerivor m sig).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]

end CategorialAlgebras.Dimensions
