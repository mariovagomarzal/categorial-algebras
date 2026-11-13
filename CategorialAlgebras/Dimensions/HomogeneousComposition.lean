import CategorialAlgebras.Dimensions.HomogeneousDerivors

/-!
# Composition of homogeneous dimension derivors

A partial map of composition dimensions records whether a dimension is retained
or made discrete. Its Kleisli composition computes the underlying derivors.
Cell-domain equations are then compared separately.
-/

universe i j k u v

namespace CategorialAlgebras.Dimensions

variable {I : Type i} {J : Type j} {K : Type k}
variable {S : Type u} (sig : Signature.{u, v} S)

/-- A partial map of composition dimensions interprets missing dimensions by variables. -/
def homogeneousDimensionDerivor (f : I → Option J) :
    Derivor (Homogeneous.Symbol I sig) (Homogeneous.Symbol J sig) where
  sortMap := id
  image
    | .base σ => .app (.base σ) (fun j => .var (Word.position _ j))
    | .source k s => match f k with
      | some j => Homogeneous.unary (.source j s) (.var (Word.position _ 0))
      | none => .var (Word.position _ 0)
    | .target k s => match f k with
      | some j => Homogeneous.unary (.target j s) (.var (Word.position _ 0))
      | none => .var (Word.position _ 0)
    | .comp k _ => match f k with
      | some j => Homogeneous.binary j (.var (Word.position _ 0)) (.var (Word.position _ 1))
      | none => .var (Word.position _ 0)

/-- The partial dimension map determines the image of each source. -/
@[simp] theorem homogeneousDimensionDerivor_source (f : I → Option J) (k : I) (s : S) :
    (homogeneousDimensionDerivor sig f).image (.source k s) =
      match f k with
      | some j => Homogeneous.unary (.source j s) (.var (Word.position _ 0))
      | none => .var (Word.position _ 0) := rfl

/-- The partial dimension map determines the image of each target. -/
@[simp] theorem homogeneousDimensionDerivor_target (f : I → Option J) (k : I) (s : S) :
    (homogeneousDimensionDerivor sig f).image (.target k s) =
      match f k with
      | some j => Homogeneous.unary (.target j s) (.var (Word.position _ 0))
      | none => .var (Word.position _ 0) := rfl

/-- The partial dimension map determines the image of each comp. -/
@[simp] theorem homogeneousDimensionDerivor_comp (f : I → Option J) (k : I) (s : S) :
    (homogeneousDimensionDerivor sig f).image (.comp k s) =
      match f k with
      | some j => Homogeneous.binary j (.var (Word.position _ 0)) (.var (Word.position _ 1))
      | none => .var (Word.position _ 0) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Partial dimension maps compose by binding their optional images. -/
theorem homogeneousDimensionDerivor_compose (f : I → Option J) (g : J → Option K) :
    (homogeneousDimensionDerivor sig f).comp (homogeneousDimensionDerivor sig g) =
      homogeneousDimensionDerivor sig (fun k => (f k).bind g) := by
  apply Derivor.ext (c := (homogeneousDimensionDerivor sig f).comp
    (homogeneousDimensionDerivor sig g)) (d := homogeneousDimensionDerivor sig _) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base σ => exact Derivor.translate_symbol (homogeneousDimensionDerivor sig g) (.base σ)
  | source k s =>
    cases hf : f k with
    | none =>
      simp only [Derivor.comp, homogeneousDimensionDerivor_source, hf, Option.bind_none,
        Derivor.translate_var]
      rfl
    | some j =>
      cases hg : g j with
      | none =>
        simp only [Derivor.comp, homogeneousDimensionDerivor_source, hf, Option.bind_some,
          Homogeneous.unary, Derivor.translate_app,
          homogeneousDimensionDerivor_source, hg, Term.substFamily]
        erw [homogeneousDimensionDerivor_source, hg]
        rfl
      | some l =>
        simp only [Derivor.comp, homogeneousDimensionDerivor_source, hf, Option.bind_some,
          Homogeneous.unary, Derivor.translate_app,
          homogeneousDimensionDerivor_source, hg, Term.substFamily]
        erw [homogeneousDimensionDerivor_source, hg]
        change Term.app (sig := Homogeneous.Symbol K sig) (.source l s) _ = _
        apply congrArg (Term.app (sig := Homogeneous.Symbol K sig) (.source l s))
        funext q
        fin_cases q
        rfl
  | target k s =>
    cases hf : f k with
    | none =>
      simp only [Derivor.comp, homogeneousDimensionDerivor_target, hf, Option.bind_none,
        Derivor.translate_var]
      rfl
    | some j =>
      cases hg : g j with
      | none =>
        simp only [Derivor.comp, homogeneousDimensionDerivor_target, hf, Option.bind_some,
          Homogeneous.unary, Derivor.translate_app,
          homogeneousDimensionDerivor_target, hg, Term.substFamily]
        erw [homogeneousDimensionDerivor_target, hg]
        rfl
      | some l =>
        simp only [Derivor.comp, homogeneousDimensionDerivor_target, hf, Option.bind_some,
          Homogeneous.unary, Derivor.translate_app,
          homogeneousDimensionDerivor_target, hg, Term.substFamily]
        erw [homogeneousDimensionDerivor_target, hg]
        change Term.app (sig := Homogeneous.Symbol K sig) (.target l s) _ = _
        apply congrArg (Term.app (sig := Homogeneous.Symbol K sig) (.target l s))
        funext q
        fin_cases q
        rfl
  | comp k s =>
    cases hf : f k with
    | none =>
      simp only [Derivor.comp, homogeneousDimensionDerivor_comp, hf, Option.bind_none,
        Derivor.translate_var]
      rfl
    | some j =>
      cases hg : g j with
      | none =>
        simp only [Derivor.comp, homogeneousDimensionDerivor_comp, hf, Option.bind_some,
          Homogeneous.binary, Derivor.translate_app,
          homogeneousDimensionDerivor_comp, hg, Term.substFamily, Term.subst_var]
        rfl
      | some l =>
        simp only [Derivor.comp, homogeneousDimensionDerivor_comp, hf, Option.bind_some,
          Homogeneous.binary, Derivor.translate_app,
          homogeneousDimensionDerivor_comp, hg, Term.substFamily, Term.subst_app]
        apply congrArg (Term.app (sig := Homogeneous.Symbol K sig) (.comp l s))
        funext q
        fin_cases q <;> rfl

/-- Discretization retains precisely the composition dimensions below the cutoff. -/
theorem homogeneousDiscretizationDerivor_eq (n m : ℕ) :
    homogeneousDiscretizationDerivor sig n m = homogeneousDimensionDerivor sig
      (fun k : Fin n => if hk : k.val < m then some ⟨k.val, hk⟩ else none) := by
  apply Derivor.ext (c := homogeneousDiscretizationDerivor sig n m)
    (d := homogeneousDimensionDerivor sig _) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base σ => rfl
  | source k s => dsimp [homogeneousDiscretizationDerivor, homogeneousDimensionDerivor]; split <;> rfl
  | target k s => dsimp [homogeneousDiscretizationDerivor, homogeneousDimensionDerivor]; split <;> rfl
  | comp k s => dsimp [homogeneousDiscretizationDerivor, homogeneousDimensionDerivor]; split <;> rfl

/-- Truncation includes each available composition dimension. -/
theorem homogeneousTruncationDerivor_eq {m n : ℕ} (h : m ≤ n) :
    homogeneousTruncationDerivor sig h =
      homogeneousDimensionDerivor sig (fun k => some (dimensionInclusion h k)) := by
  apply Derivor.ext (c := homogeneousTruncationDerivor sig h)
    (d := homogeneousDimensionDerivor sig _) rfl
  apply heq_of_eq
  funext a s σ
  cases σ <;> rfl

/-- Successive homogeneous discretizations have the same underlying derivor. -/
theorem homogeneousDiscretization_comp_derivor {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (homogeneousDiscretization sig hnp).toDerivor.comp
        (homogeneousDiscretization sig hmn).toDerivor =
      (homogeneousDiscretization sig (le_trans hmn hnp)).toDerivor := by
  change (homogeneousDiscretizationDerivor sig p n).comp
    (homogeneousDiscretizationDerivor sig n m) = homogeneousDiscretizationDerivor sig p m
  rw [homogeneousDiscretizationDerivor_eq, homogeneousDiscretizationDerivor_eq,
    homogeneousDiscretizationDerivor_eq, homogeneousDimensionDerivor_compose]
  congr 1
  funext k
  by_cases hk : k.val < m
  · simp only [dite_eq_left (lt_of_lt_of_le hk hmn), Option.bind_some, dite_eq_left hk]
  · by_cases hn : k.val < n
    · simp only [dite_eq_left hn, Option.bind_some, dite_eq_right hk]
    · simp only [dite_eq_right hn, Option.bind_none, dite_eq_right hk]

/-- Successive homogeneous discretizations are equal as generalized hep-derivors. -/
theorem homogeneousDiscretization_comp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (homogeneousDiscretization sig hnp).comp (homogeneousDiscretization sig hmn) =
      homogeneousDiscretization sig (le_trans hmn hnp) := by
  apply GeneralizedHepDerivor.ext (homogeneousDiscretization_comp_derivor sig hmn hnp)
  apply heq_of_eq
  funext s
  change ⊥ ⊔ (homogeneousDiscretizationDerivor sig n m).translateSingletonSet _ ⊥ = ⊥
  rw [Derivor.translateSingletonSet_empty, bot_sup_eq]

/-- Successive homogeneous truncations have the same underlying inclusion derivor. -/
theorem homogeneousTruncation_comp_derivor {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (homogeneousTruncation sig hmn).toDerivor.comp (homogeneousTruncation sig hnp).toDerivor =
      (homogeneousTruncation sig (le_trans hmn hnp)).toDerivor := by
  change (homogeneousTruncationDerivor sig hmn).comp (homogeneousTruncationDerivor sig hnp) =
    homogeneousTruncationDerivor sig (le_trans hmn hnp)
  rw [homogeneousTruncationDerivor_eq, homogeneousTruncationDerivor_eq,
    homogeneousTruncationDerivor_eq, homogeneousDimensionDerivor_compose]
  rfl

/-- Truncation followed by discretization above its initial dimension has the underlying
derivor of a discretization. -/
theorem homogeneousMixed_upper_derivor {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (homogeneousTruncation sig hnp).toDerivor.comp
        (homogeneousDiscretization sig (le_trans hmn hnp)).toDerivor =
      (homogeneousDiscretization sig hmn).toDerivor := by
  change (homogeneousTruncationDerivor sig hnp).comp
    (homogeneousDiscretizationDerivor sig p m) = homogeneousDiscretizationDerivor sig n m
  rw [homogeneousTruncationDerivor_eq, homogeneousDiscretizationDerivor_eq,
    homogeneousDiscretizationDerivor_eq, homogeneousDimensionDerivor_compose]
  rfl

/-- Truncation followed by discretization below its initial dimension has the underlying
derivor of a truncation. -/
theorem homogeneousMixed_lower_derivor {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (homogeneousTruncation sig (le_trans hmn hnp)).toDerivor.comp
        (homogeneousDiscretization sig hnp).toDerivor =
      (homogeneousTruncation sig hmn).toDerivor := by
  change (homogeneousTruncationDerivor sig (le_trans hmn hnp)).comp
    (homogeneousDiscretizationDerivor sig p n) = homogeneousTruncationDerivor sig hmn
  rw [homogeneousTruncationDerivor_eq, homogeneousDiscretizationDerivor_eq,
    homogeneousTruncationDerivor_eq, homogeneousDimensionDerivor_compose]
  congr 1
  funext k
  change (if hk : k.val < n then some (⟨k.val, hk⟩ : Fin n) else none) = _
  rw [dite_eq_left (lt_of_lt_of_le k.isLt hmn)]
  rfl

/-- The homogeneous round trip has the identity underlying derivor. -/
theorem homogeneousTruncation_discretization_derivor {m n : ℕ} (h : m ≤ n) :
    (homogeneousTruncation sig h).toDerivor.comp (homogeneousDiscretization sig h).toDerivor =
      Derivor.identity (Homogeneous.Symbol (Fin m) sig) := by
  have he := homogeneousMixed_lower_derivor sig (le_refl m) h
  rw [homogeneousTruncation_self] at he
  exact he

end CategorialAlgebras.Dimensions
