import CategorialAlgebras.Dimensions.HomogeneousComposition
import CategorialAlgebras.Dimensions.HomogeneousModels

/-!
# Syntactic domains and homogeneous cells

Successive proper truncations retain two fixed-source equations. A round trip
through a larger discrete dimension retains a reflexive equation. These domains
are syntactically different from the direct domains, although they select the
same cells in models.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open Presentations

variable {S : Type u} (sig : Signature.{u, v} S)

/-- The reflexive existence equation in a single positional variable. -/
def reflexiveEquation {n : ℕ} (s : S) :
    EEquation (Homogeneous.Symbol (Fin n) sig) (Word.Variables [s]) s :=
  (.var (Word.position _ 0), .var (Word.position _ 0))

/-- Translating a sorted singleton gives the singleton of the translated equation. -/
theorem translateSingletonSet_singleton {T : Type*} {σ : Signature S} {τ : Signature T}
    (c : Derivor σ τ) {s : S} (e : EEquation σ (Word.Variables [s]) s) :
    c.translateSingletonSet s (Homogeneous.singletonEquation e) =
      Heterogeneous.singletonEquation (c.translateSingleton s e.1, c.translateSingleton s e.2) := by
  funext t
  ext q
  constructor
  · rintro ⟨r, hr, p, ⟨hs, hp⟩, he⟩
    cases hs
    cases hp
    exact ⟨hr, he⟩
  · rintro ⟨hr, he⟩
    exact ⟨s, hr, e, ⟨rfl, rfl⟩, he⟩

/-- Inclusion translates the cutoff equation to the same cutoff in the larger signature. -/
theorem truncation_translate_equation {m n : ℕ} (h : m ≤ n) (k : Fin m) (s : S) :
    (homogeneousTruncationDerivor sig h).translateSingletonSet s
        (Homogeneous.singletonEquation (truncationEquation sig k s)) =
      Homogeneous.singletonEquation (truncationEquation sig (dimensionInclusion h k) s) := by
  rw [translateSingletonSet_singleton]
  congr 1
  apply Prod.ext
  · rfl
  · change Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (.source (dimensionInclusion h k) s) _ = _
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (.source (dimensionInclusion h k) s))
    funext q
    fin_cases q
    rfl

/-- Discretization sends a retained cutoff equation to the corresponding fixed-source equation. -/
theorem discretization_translate_equation_of_lt {m n : ℕ} (_h : m ≤ n) (k : Fin n)
    (hk : k.val < m) (s : S) :
    (homogeneousDiscretizationDerivor sig n m).translateSingletonSet s
        (Homogeneous.singletonEquation (truncationEquation sig k s)) =
      Homogeneous.singletonEquation (truncationEquation sig ⟨k.val, hk⟩ s) := by
  rw [translateSingletonSet_singleton]
  congr 1
  apply Prod.ext
  · rfl
  · change Term.substFamily _ (if hk : k.val < m then _ else _) = _
    erw [dite_eq_left hk]
    change Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.source ⟨k.val, hk⟩ s) _ = _
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.source ⟨k.val, hk⟩ s))
    funext q
    fin_cases q
    rfl

/-- Discretization sends a discarded cutoff equation to a reflexive equation. -/
theorem discretization_translate_equation_of_le {m n : ℕ} (_h : m ≤ n) (k : Fin n)
    (hk : m ≤ k.val) (s : S) :
    (homogeneousDiscretizationDerivor sig n m).translateSingletonSet s
        (Homogeneous.singletonEquation (truncationEquation sig k s)) =
      Homogeneous.singletonEquation (reflexiveEquation (n := m) sig s) := by
  rw [translateSingletonSet_singleton]
  congr 1
  apply Prod.ext
  · rfl
  · change Term.substFamily _ (if hk : k.val < m then _ else _) = _
    erw [dite_eq_right (not_lt_of_ge hk)]
    rfl

/-- Two successive proper truncations retain both fixed-source equations. -/
theorem homogeneousTruncation_comp_domain {m n p : ℕ} (hmn : m < n) (hnp : n < p) (s : S) :
    ((homogeneousTruncation sig hmn.le).comp (homogeneousTruncation sig hnp.le)).domain s =
      Homogeneous.singletonEquation (truncationEquation sig ⟨n, hnp⟩ s) ⊔
        Homogeneous.singletonEquation (truncationEquation sig ⟨m, lt_trans hmn hnp⟩ s) := by
  change (homogeneousTruncation sig hnp.le).domain s ⊔
    (homogeneousTruncationDerivor sig hnp.le).translateSingletonSet s
      ((homogeneousTruncation sig hmn.le).domain s) = _
  rw [homogeneousTruncation_domain_of_lt sig hnp, homogeneousTruncation_domain_of_lt sig hmn,
    truncation_translate_equation]
  rfl

/-- A proper truncation after discretization above the initial dimension retains a
reflexive equation instead of an empty domain. -/
theorem homogeneousMixed_upper_domain {m n p : ℕ} (hmn : m ≤ n) (hnp : n < p) (s : S) :
    ((homogeneousTruncation sig hnp.le).comp
      (homogeneousDiscretization sig (le_trans hmn hnp.le))).domain s =
        Homogeneous.singletonEquation (reflexiveEquation (n := m) sig s) := by
  change ⊥ ⊔ (homogeneousDiscretizationDerivor sig p m).translateSingletonSet s
    ((homogeneousTruncation sig hnp.le).domain s) = _
  erw [homogeneousTruncation_domain_of_lt sig hnp,
    discretization_translate_equation_of_le sig (le_trans hmn hnp.le) _ hmn, bot_sup_eq]

/-- A proper homogeneous round trip has a singleton reflexive domain. -/
theorem homogeneousTruncation_discretization_domain {m n : ℕ} (h : m < n) (s : S) :
    ((homogeneousTruncation sig h.le).comp (homogeneousDiscretization sig h.le)).domain s =
      Homogeneous.singletonEquation (reflexiveEquation (n := m) sig s) :=
  homogeneousMixed_upper_domain sig (le_refl m) h s

/-- Below the initial dimension, the mixed composition has exactly the truncation domain. -/
theorem homogeneousMixed_lower {m n p : ℕ} (hmn : m < n) (hnp : n ≤ p) :
    (homogeneousTruncation sig (le_trans hmn.le hnp)).comp
      (homogeneousDiscretization sig hnp) = homogeneousTruncation sig hmn.le := by
  apply GeneralizedHepDerivor.ext (homogeneousMixed_lower_derivor sig hmn.le hnp)
  apply heq_of_eq
  funext s
  change ⊥ ⊔ (homogeneousDiscretizationDerivor sig p n).translateSingletonSet s
    ((homogeneousTruncation sig (le_trans hmn.le hnp)).domain s) = _
  have hmp : m < p := lt_of_lt_of_le hmn hnp
  erw [homogeneousTruncation_domain_of_lt sig hmp,
    discretization_translate_equation_of_lt sig hnp _ hmn, bot_sup_eq,
    homogeneousTruncation_domain_of_lt sig hmn]

/-- Fixed-source equations in different dimensions are different syntactic equations. -/
theorem truncationEquation_ne {n : ℕ} {j k : Fin n} (h : j ≠ k) (s : S) :
    truncationEquation sig j s ≠ truncationEquation sig k s := by
  intro he
  have he' := congrArg Prod.snd he
  have hj : (⟨[s], s, Homogeneous.Symbol.source j s⟩ : OperationSymbol
      (Homogeneous.Symbol (Fin n) sig)) ∈ (truncationEquation sig j s).2.symbols :=
    Or.inl rfl
  rw [he'] at hj
  change _ ∈ Term.symbols (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.source k s) _) at hj
  rcases hj with he | ⟨q, hq⟩
  · have hejk : j = k := by
      have he0 := Set.mem_singleton_iff.mp he
      cases he0
      rfl
    exact h hejk
  · fin_cases q
    exact hq.elim

/-- Successive proper homogeneous truncations are unequal generalized hep-derivors
when there is at least one sort.

**Formally weaker** than the informal statement. Informally, the two derivors are different for
every set of sorts; here the set of sorts must be nonempty, since with no sorts the two derivors
coincide. -/
theorem homogeneousTruncation_comp_ne [Nonempty S] {m n p : ℕ}
    (hmn : m < n) (hnp : n < p) :
    (homogeneousTruncation sig hmn.le).comp (homogeneousTruncation sig hnp.le) ≠
      homogeneousTruncation sig (le_trans hmn.le hnp.le) := by
  intro he
  obtain ⟨s⟩ := ‹Nonempty S›
  have hd0 : HEq
      ((homogeneousTruncation sig hmn.le).comp (homogeneousTruncation sig hnp.le)).domain
      (homogeneousTruncation sig (le_trans hmn.le hnp.le)).domain := hepDomain_heq he
  have hd := congrFun (congrFun (eq_of_heq hd0) s) s
  rw [homogeneousTruncation_comp_domain sig hmn hnp, homogeneousTruncation_domain_of_lt sig
    (lt_trans hmn hnp)] at hd
  have hm : truncationEquation sig ⟨n, hnp⟩ s ∈
      (Homogeneous.singletonEquation (truncationEquation sig ⟨n, hnp⟩ s) ⊔
        Homogeneous.singletonEquation (truncationEquation sig ⟨m, lt_trans hmn hnp⟩ s)) s :=
    Or.inl ⟨rfl, rfl⟩
  rw [hd] at hm
  obtain ⟨hs, hm⟩ := hm
  have heq : truncationEquation sig ⟨n, hnp⟩ s =
      truncationEquation sig ⟨m, lt_trans hmn hnp⟩ s := by simpa using hm
  exact truncationEquation_ne sig (j := ⟨n, hnp⟩) (k := ⟨m, lt_trans hmn hnp⟩)
    (by intro h; have hv : n = m := congrArg Fin.val h; omega) s heq

/-- The homogeneous mixed upper composite is unequal to discretization when the
intermediate truncation is proper and there is at least one sort.

**Formally weaker** than the informal statement. Informally, the two derivors are different for
every set of sorts; here the set of sorts must be nonempty, since with no sorts the two derivors
coincide. -/
theorem homogeneousMixed_upper_ne [Nonempty S] {m n p : ℕ}
    (hmn : m ≤ n) (hnp : n < p) :
    (homogeneousTruncation sig hnp.le).comp
      (homogeneousDiscretization sig (le_trans hmn hnp.le)) ≠
        homogeneousDiscretization sig hmn := by
  intro he
  obtain ⟨s⟩ := ‹Nonempty S›
  have hd0 : HEq
      ((homogeneousTruncation sig hnp.le).comp
        (homogeneousDiscretization sig (le_trans hmn hnp.le))).domain
      (homogeneousDiscretization sig hmn).domain := hepDomain_heq he
  have hd := congrFun (congrFun (eq_of_heq hd0) s) s
  rw [homogeneousMixed_upper_domain sig hmn hnp, homogeneousDiscretization_domain] at hd
  have hm : reflexiveEquation (n := m) sig s ∈
      Homogeneous.singletonEquation (reflexiveEquation (n := m) sig s) s := ⟨rfl, rfl⟩
  rw [hd] at hm
  exact hm.elim

/-- A proper homogeneous round trip is unequal to the identity generalized derivor.

**Formally weaker** than the informal statement. Informally, the two derivors are different for
every set of sorts; here the set of sorts must be nonempty, since with no sorts the two derivors
coincide. -/
theorem homogeneousTruncation_discretization_ne [Nonempty S] {m n : ℕ} (h : m < n) :
    (homogeneousTruncation sig h.le).comp (homogeneousDiscretization sig h.le) ≠
      GeneralizedHepDerivor.identity (Homogeneous.hepSignature (Fin m) sig) := by
  simpa only [homogeneousDiscretization_self] using
    homogeneousMixed_upper_ne sig (le_refl m) h

end CategorialAlgebras.Dimensions
