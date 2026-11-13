import CategorialAlgebras.Dimensions.HeterogeneousDerivors

/-!
# Composition of heterogeneous dimension derivors

Monotone dimension changes compose strictly, including their empty domains.
This gives the finite discretization, truncation and mixed composition laws.
-/

universe i j k u v

namespace CategorialAlgebras.Dimensions

variable {I : Type i} {J : Type j} {K : Type k}
  [LinearOrder I] [LinearOrder J] [LinearOrder K]
variable {S : Type u} (sig : Signature.{u, v} S)

set_option backward.isDefEq.respectTransparency false in
/-- Monotone changes of dimension compose as derivors. -/
theorem heterogeneousDimensionDerivor_compose (f : I →o J) (g : J →o K) :
 (heterogeneousDimensionDerivor sig f).comp (heterogeneousDimensionDerivor sig g) =
 heterogeneousDimensionDerivor sig (g.comp f) := by
 apply Derivor.ext (c := (heterogeneousDimensionDerivor sig f).comp (heterogeneousDimensionDerivor sig g))
   (d := heterogeneousDimensionDerivor sig (g.comp f)) rfl
 apply heq_of_eq
 funext a s σ
 cases σ with
 | @base k a s σ =>
   change Term.app (sig := Heterogeneous.Symbol K sig) (.base (g (f k)) σ) _ = _
   apply congrArg (Term.app (sig := Heterogeneous.Symbol K sig) (.base (g (f k)) σ))
   funext q
   simp [heterogeneousDimensionDerivor, Term.eval, Word.valuation,
     Derivor.positionMap, dimensionSortMap, List.get_eq_getElem]
   apply eq_of_heq
   erw [eqRec_heq_iff]
   have hv {s t : K × S} (p q : Fin (Heterogeneous.dimensionWord k a).length)
       (hp : dimensionSortMap (fun i => g (f i)) ((Heterogeneous.dimensionWord k a).get p) = s)
       (hq : dimensionSortMap (fun i => g (f i)) ((Heterogeneous.dimensionWord k a).get q) = t)
       (he : p = q) :
       HEq (Term.var (sig := Heterogeneous.Symbol K sig)
         (X := Word.MappedVariables (dimensionSortMap (fun i => g (f i)))
           (Heterogeneous.dimensionWord k a)) ⟨p, hp⟩)
         (Term.var (sig := Heterogeneous.Symbol K sig)
           (X := Word.MappedVariables (dimensionSortMap (fun i => g (f i)))
             (Heterogeneous.dimensionWord k a)) ⟨q, hq⟩) := by
     cases he
     cases hp
     cases hq
     rfl
   exact hv _ _ _ _ rfl
 | @source j k h s =>
   by_cases hf : f j < f k
   · by_cases hg : g (f j) < g (f k)
     · simp only [Derivor.comp, heterogeneousDimensionDerivor_source, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
         hf, hg, dite_true, Heterogeneous.boundary, Heterogeneous.Symbol.boundary,
         Bool.false_eq_true, ite_false, Heterogeneous.unary, Derivor.translate_app,
         Term.substFamily, Term.subst_app]
       erw [dite_eq_left hg]
       change Term.app (sig := Heterogeneous.Symbol K sig) (.source hg s) _ = _
       apply congrArg (Term.app (sig := Heterogeneous.Symbol K sig) (.source hg s))
       funext q
       fin_cases q
       rfl
     · simp only [Derivor.comp, heterogeneousDimensionDerivor_source, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
         hf, hg, dite_true, dite_false, Heterogeneous.boundary, Heterogeneous.Symbol.boundary,
         Bool.false_eq_true, ite_false, Heterogeneous.unary, Derivor.translate_app,
         Term.substFamily, Term.subst_var]
       erw [dite_eq_right hg]
       dsimp only [Word.valuation]
       apply eq_of_heq
       erw [eqRec_heq_iff]
       exact positionalTerm_heq _ _ _ _ rfl
   · have he := le_antisymm (f.monotone h.le) (le_of_not_gt hf)
     have hg : ¬ g (f j) < g (f k) := by rw [he]; exact lt_irrefl _
     simp only [Derivor.comp, heterogeneousDimensionDerivor_source, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
       hf, dite_false, Derivor.translate_var]
     erw [dite_eq_right hg]
     rfl
 | @target j k h s =>
   by_cases hf : f j < f k
   · by_cases hg : g (f j) < g (f k)
     · simp only [Derivor.comp, heterogeneousDimensionDerivor_target, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
         hf, hg, dite_true, Heterogeneous.boundary, Heterogeneous.Symbol.boundary,
         ite_true, Heterogeneous.unary, Derivor.translate_app,
         Term.substFamily, Term.subst_app]
       erw [dite_eq_left hg]
       change Term.app (sig := Heterogeneous.Symbol K sig) (.target hg s) _ = _
       apply congrArg (Term.app (sig := Heterogeneous.Symbol K sig) (.target hg s))
       funext q
       fin_cases q
       rfl
     · simp only [Derivor.comp, heterogeneousDimensionDerivor_target, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
         hf, hg, dite_true, dite_false, Heterogeneous.boundary, Heterogeneous.Symbol.boundary,
         ite_true, Heterogeneous.unary, Derivor.translate_app,
         Term.substFamily, Term.subst_var]
       erw [dite_eq_right hg]
       dsimp only [Word.valuation]
       apply eq_of_heq
       erw [eqRec_heq_iff]
       exact positionalTerm_heq _ _ _ _ rfl
   · have he := le_antisymm (f.monotone h.le) (le_of_not_gt hf)
     have hg : ¬ g (f j) < g (f k) := by rw [he]; exact lt_irrefl _
     simp only [Derivor.comp, heterogeneousDimensionDerivor_target, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
       hf, dite_false, Derivor.translate_var]
     erw [dite_eq_right hg]
     rfl
 | @identity j k h s =>
   by_cases hf : f j < f k
   · by_cases hg : g (f j) < g (f k)
     · simp only [Derivor.comp, heterogeneousDimensionDerivor_identity, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
         hf, hg, dite_true, Heterogeneous.identityTerm, Heterogeneous.unary, Derivor.translate_app,
         Term.substFamily, Term.subst_app]
       erw [dite_eq_left hg]
       change Term.app (sig := Heterogeneous.Symbol K sig) (.identity hg s) _ = _
       apply congrArg (Term.app (sig := Heterogeneous.Symbol K sig) (.identity hg s))
       funext q
       fin_cases q
       rfl
     · simp only [Derivor.comp, heterogeneousDimensionDerivor_identity, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
         hf, hg, dite_true, dite_false, Heterogeneous.identityTerm, Heterogeneous.unary, Derivor.translate_app,
         Term.substFamily, Term.subst_var]
       erw [dite_eq_right hg]
       dsimp only [Word.valuation]
       apply eq_of_heq
       erw [eqRec_heq_iff]
       exact positionalTerm_heq _ _ _ _ rfl
   · have he := le_antisymm (f.monotone h.le) (le_of_not_gt hf)
     have hg : ¬ g (f j) < g (f k) := by rw [he]; exact lt_irrefl _
     simp only [Derivor.comp, heterogeneousDimensionDerivor_identity, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
       hf, dite_false, Derivor.translate_var]
     erw [dite_eq_right hg]
     rfl
 | @comp j k h s =>
   by_cases hf : f j < f k
   · by_cases hg : g (f j) < g (f k)
     · simp only [Derivor.comp, heterogeneousDimensionDerivor_comp, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
         hf, hg, dite_true, Heterogeneous.binary, Derivor.translate_app,
         Term.substFamily, Term.subst_app]
       erw [dite_eq_left hg]
       change Term.app (sig := Heterogeneous.Symbol K sig) (.comp hg s) _ = _
       apply congrArg (Term.app (sig := Heterogeneous.Symbol K sig) (.comp hg s))
       funext q
       fin_cases q <;> rfl
     · simp only [Derivor.comp, heterogeneousDimensionDerivor_comp, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
         hf, hg, dite_true, dite_false, Heterogeneous.binary, Derivor.translate_app,
         Term.substFamily, Term.subst_var]
       erw [dite_eq_right hg]
       rfl
   · have he := le_antisymm (f.monotone h.le) (le_of_not_gt hf)
     have hg : ¬ g (f j) < g (f k) := by rw [he]; exact lt_irrefl _
     simp only [Derivor.comp, heterogeneousDimensionDerivor_comp, heterogeneousDimensionDerivor_sortMap, OrderHom.comp,
       hf, dite_false, Derivor.translate_var]
     erw [dite_eq_right hg]
     rfl



/-- The identity dimension map gives the identity underlying derivor. -/
theorem heterogeneousDimensionDerivor_id :
    heterogeneousDimensionDerivor sig (OrderHom.id : I →o I) =
      Derivor.identity (Heterogeneous.Symbol I sig) := by
  apply Derivor.ext (c := heterogeneousDimensionDerivor sig OrderHom.id)
    (d := Derivor.identity _) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base k σ => rfl
  | source h s =>
    erw [heterogeneousDimensionDerivor_source, dite_eq_left h]
    apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.source h s))
    funext q
    fin_cases q
    rfl
  | target h s =>
    erw [heterogeneousDimensionDerivor_target, dite_eq_left h]
    apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.target h s))
    funext q
    fin_cases q
    rfl
  | identity h s =>
    erw [heterogeneousDimensionDerivor_identity, dite_eq_left h]
    apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.identity h s))
    funext q
    fin_cases q
    rfl
  | comp h s =>
    erw [heterogeneousDimensionDerivor_comp, dite_eq_left h]
    apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.comp h s))
    funext q
    fin_cases q <;> rfl

/-- Monotone dimension changes compose strictly as generalized hep-derivors. -/
theorem heterogeneousDimension_compose (f : I →o J) (g : J →o K) :
    (heterogeneousDimension sig f).comp (heterogeneousDimension sig g) =
      heterogeneousDimension sig (g.comp f) := by
  apply GeneralizedHepDerivor.ext (heterogeneousDimensionDerivor_compose sig f g)
  apply heq_of_eq
  funext p
  change ⊥ ⊔ (heterogeneousDimensionDerivor sig g).translateSingletonSet _ ⊥ = ⊥
  rw [Derivor.translateSingletonSet_empty, bot_sup_eq]

/-- The identity dimension map gives the identity generalized hep-derivor. -/
@[simp] theorem heterogeneousDimension_id :
    heterogeneousDimension sig (OrderHom.id : I →o I) =
      GeneralizedHepDerivor.identity (Heterogeneous.hepSignature I sig) := by
  apply GeneralizedHepDerivor.ext (heterogeneousDimensionDerivor_id sig)
  rfl

/-- Discretization in equal dimensions is the identity generalized hep-derivor. -/
@[simp] theorem heterogeneousDiscretization_self (n : ℕ) :
    heterogeneousDiscretization sig (le_refl n) =
      GeneralizedHepDerivor.identity (Heterogeneous.hepSignature (Fin (n + 1)) sig) := by
  have he : (clampDimension n : Fin (n + 1) →o Fin (n + 1)) = OrderHom.id := by
    apply OrderHom.ext
    funext k
    exact clampDimension_self n k
  unfold heterogeneousDiscretization
  rw [he, heterogeneousDimension_id]

/-- Truncation in equal dimensions is the identity generalized hep-derivor. -/
@[simp] theorem heterogeneousTruncation_self (n : ℕ) :
    heterogeneousTruncation sig (le_refl n) =
      GeneralizedHepDerivor.identity (Heterogeneous.hepSignature (Fin (n + 1)) sig) := by
  have he : (cellInclusion (le_refl n)).toOrderHom = OrderHom.id := by ext k; rfl
  unfold heterogeneousTruncation
  rw [he, heterogeneousDimension_id]

/-- Successive heterogeneous discretizations compose to the smaller cutoff. -/
theorem heterogeneousDiscretization_comp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (heterogeneousDiscretization sig hnp).comp (heterogeneousDiscretization sig hmn) =
      heterogeneousDiscretization sig (le_trans hmn hnp) := by
  unfold heterogeneousDiscretization
  rw [heterogeneousDimension_compose]
  congr 1
  apply OrderHom.ext
  funext k
  exact clampDimension_clampDimension hmn k

/-- Successive heterogeneous truncations compose to the same inclusion. -/
theorem heterogeneousTruncation_comp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (heterogeneousTruncation sig hmn).comp (heterogeneousTruncation sig hnp) =
      heterogeneousTruncation sig (le_trans hmn hnp) := by
  unfold heterogeneousTruncation
  rw [heterogeneousDimension_compose]
  rfl

/-- Heterogeneous truncation followed by discretization is the identity derivor. -/
theorem heterogeneousTruncation_discretization {m n : ℕ} (h : m ≤ n) :
    (heterogeneousTruncation sig h).comp (heterogeneousDiscretization sig h) =
      GeneralizedHepDerivor.identity (Heterogeneous.hepSignature (Fin (m + 1)) sig) := by
  unfold heterogeneousTruncation heterogeneousDiscretization
  rw [heterogeneousDimension_compose]
  have he : (clampDimension m).comp (cellInclusion h).toOrderHom = OrderHom.id := by
    apply OrderHom.ext
    funext k
    exact clampDimension_inclusion h k
  rw [he, heterogeneousDimension_id]

/-- Truncating a discretization above its initial dimension gives a discretization. -/
theorem heterogeneousMixed_upper {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (heterogeneousTruncation sig hnp).comp
        (heterogeneousDiscretization sig (le_trans hmn hnp)) =
      heterogeneousDiscretization sig hmn := by
  unfold heterogeneousTruncation heterogeneousDiscretization
  rw [heterogeneousDimension_compose]
  rfl

/-- Truncating a discretization below its initial dimension gives a truncation. -/
theorem heterogeneousMixed_lower {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (heterogeneousTruncation sig (le_trans hmn hnp)).comp
        (heterogeneousDiscretization sig hnp) = heterogeneousTruncation sig hmn := by
  unfold heterogeneousTruncation heterogeneousDiscretization
  rw [heterogeneousDimension_compose]
  congr 1
  apply OrderHom.ext
  funext k
  apply Fin.ext
  exact min_eq_left (le_trans (Nat.le_of_lt_succ k.isLt) hmn)

end CategorialAlgebras.Dimensions
