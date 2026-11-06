import CategorialAlgebras.ChangeOfSignature.Derivors
import CategorialAlgebras.Presentations.Unification
import CategorialAlgebras.Dimensions.HomogeneousDomains
import CategorialAlgebras.Dimensions.UnificationDerivors

/-!
# Change of signature commutes with the presentation and dimension derivors

The generalized hep-derivors of a change of signature commute, in the category of
hierarchical signatures and generalized hep-derivors, with those of graduation,
unification, discretization and truncation:
$$\mathbf{c}^{(n)}\circ\mathbf{Gd}^{(n)}_{\Sigma}=\mathbf{Gd}^{(n)}_{\Lambda}\circ
\mathbf{c}^{\mathrm{htg}(n)},\qquad
\mathbf{c}^{\mathrm{htg}(n)}\circ\mathbf{Uf}^{(n)}_{\Sigma}=\mathbf{Uf}^{(n)}_{\Lambda}\circ
\mathbf{c}^{(n)},$$
and similarly for discretization and truncation in both presentations. The heterogeneous
statements hold for every monotone change of dimensions.

The proofs compare the composite derivors. On the original operation symbols they use that
the presentation and dimension derivors send the copies of the operation symbols of the
base signature to copies, so that translation along them commutes with the inclusions of
the terms of the base signature.
-/

universe i j u v

namespace CategorialAlgebras.ChangeOfSignature

open CategoryTheory Presentations Dimensions

variable {S T : Type u} {sig : Signature.{u, v} S} {tau : Signature.{u, v} T}

/-! ## The inclusions of terms along the presentation and dimension derivors -/

/-- Graduation sends the copy $\tau_k$ of an original symbol to $\tau$: translating $P_k$
along graduation gives $P$. -/
theorem heterogeneousInclusion_comp_graduation (n : ℕ) (k : Fin (n + 1)) :
    (heterogeneousInclusion (Fin (n + 1)) k tau).comp (graduationDerivor n tau) =
      homogeneousInclusion (Fin n) tau := by
  apply Derivor.ext (c := (heterogeneousInclusion (Fin (n + 1)) k tau).comp
    (graduationDerivor n tau)) (d := homogeneousInclusion (Fin n) tau) rfl
  apply heq_of_eq
  funext a t τ
  rw [heterogeneousInclusion_comp_image]
  rfl

/-- Unification sends an original symbol $\tau$ to its top copy $\tau_n$: translating $P$
along unification gives $P_n$. -/
theorem homogeneousInclusion_comp_unification (n : ℕ) :
    (homogeneousInclusion (Fin n) tau).comp (unificationDerivor n tau) =
      heterogeneousInclusion (Fin (n + 1)) (Fin.last n) tau := by
  apply Derivor.ext (c := (homogeneousInclusion (Fin n) tau).comp (unificationDerivor n tau))
    (d := heterogeneousInclusion (Fin (n + 1)) (Fin.last n) tau) rfl
  apply heq_of_eq
  funext a t τ
  rw [homogeneousInclusion_comp_image]
  rfl

/-- Homogeneous discretization fixes the terms of the base signature. -/
theorem homogeneousInclusion_comp_discretization (n m : ℕ) :
    (homogeneousInclusion (Fin n) tau).comp (homogeneousDiscretizationDerivor tau n m) =
      homogeneousInclusion (Fin m) tau := by
  apply Derivor.ext (c := (homogeneousInclusion (Fin n) tau).comp
    (homogeneousDiscretizationDerivor tau n m)) (d := homogeneousInclusion (Fin m) tau) rfl
  apply heq_of_eq
  funext a t τ
  rw [homogeneousInclusion_comp_image]
  rfl

/-- Homogeneous truncation fixes the terms of the base signature. -/
theorem homogeneousInclusion_comp_truncation {m n : ℕ} (h : m ≤ n) :
    (homogeneousInclusion (Fin m) tau).comp (homogeneousTruncationDerivor tau h) =
      homogeneousInclusion (Fin n) tau := by
  apply Derivor.ext (c := (homogeneousInclusion (Fin m) tau).comp
    (homogeneousTruncationDerivor tau h)) (d := homogeneousInclusion (Fin n) tau) rfl
  apply heq_of_eq
  funext a t τ
  rw [homogeneousInclusion_comp_image]
  rfl

/-- A monotone change of dimensions $f$ sends $P_k$ to $P_{f(k)}$. -/
theorem heterogeneousInclusion_comp_dimension {I : Type i} {J : Type j} [LinearOrder I]
    [LinearOrder J] (f : I →o J) (k : I) :
    (heterogeneousInclusion I k tau).comp (heterogeneousDimensionDerivor tau f) =
      heterogeneousInclusion J (f k) tau := by
  apply Derivor.ext (c := (heterogeneousInclusion I k tau).comp
    (heterogeneousDimensionDerivor tau f)) (d := heterogeneousInclusion J (f k) tau) rfl
  apply heq_of_eq
  funext a t τ
  rw [heterogeneousInclusion_comp_image]
  rfl

/-! ## Graduation and unification -/

/-- Graduation commutes with the derivors of a change of signature:
$\mathbf{c}^{(n)}\circ\mathbf{Gd}^{(n)}_{\Sigma}=\mathbf{Gd}^{(n)}_{\Lambda}\circ
\mathbf{c}^{\mathrm{htg}(n)}$, domains included. -/
theorem graduation_comp (n : ℕ) (c : Derivor sig tau) :
    (graduation n sig).comp (homogeneous (Fin n) c) =
      (heterogeneous (Fin (n + 1)) c).comp (graduation n tau) := by
  apply GeneralizedHepDerivor.ext
  · apply Derivor.ext (c := (graduationDerivor n sig).comp (homogeneousDerivor (Fin n) c))
      (d := (heterogeneousDerivor (Fin (n + 1)) c).comp (graduationDerivor n tau)) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base k σ =>
      have h2 := Derivor.translate_comp (heterogeneousInclusion (Fin (n + 1)) k tau)
        (graduationDerivor n tau) (fun t x => .var (dimensionPosition k c.sortMap _ t x))
        ((graduationDerivor n tau).positionMap (heterogeneousSortMap c) _) (c.image σ)
      change Term.subst _ (homogeneousTerm (Fin n) (c.image σ)) = _
      refine (Derivor.subst_translate _ _ _ _).trans (Eq.trans ?_ h2)
      apply eq_of_heq
      apply Derivor.translate_heq (heterogeneousInclusion_comp_graduation n k).symm
      apply heq_of_eq
      funext t x
      obtain ⟨j, h⟩ := x
      cases h
      rfl
    | source h s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau)
        (.source (lowerDimension h) _))
      funext j
      fin_cases j
      rfl
    | target h s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau)
        (.target (lowerDimension h) _))
      funext j
      fin_cases j
      rfl
    | identity h s => rfl
    | comp h s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau)
        (.comp (lowerDimension h) _))
      funext j
      fin_cases j <;> rfl
  · apply heq_of_eq
    funext p
    obtain ⟨k, s⟩ := p
    change ⊥ ⊔ (homogeneousDerivor (Fin n) c).translateSingletonSet _
        ((graduation n sig).domain (k, s)) =
      (graduation n tau).domain (k, c.sortMap s) ⊔
        (graduationDerivor n tau).translateSingletonSet _ ⊥
    erw [Derivor.translateSingletonSet_empty, sup_bot_eq, bot_sup_eq]
    by_cases hk : k.val < n
    · unfold graduation
      simp only [dite_eq_left hk]
      refine (translateSingletonSet_singleton (homogeneousDerivor (Fin n) c) _).trans ?_
      congr 1
      apply Prod.ext
      · rfl
      · apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau)
          (.source ⟨k.val, hk⟩ _))
        funext j
        fin_cases j
        rfl
    · unfold graduation
      simp only [dite_eq_right hk]
      exact Derivor.translateSingletonSet_empty _ _

/-- Unification commutes with the derivors of a change of signature:
$\mathbf{c}^{\mathrm{htg}(n)}\circ\mathbf{Uf}^{(n)}_{\Sigma}=\mathbf{Uf}^{(n)}_{\Lambda}
\circ\mathbf{c}^{(n)}$, domains included. -/
theorem unification_comp (n : ℕ) (c : Derivor sig tau) :
    (unification n sig).comp (heterogeneous (Fin (n + 1)) c) =
      (homogeneous (Fin n) c).comp (unification n tau) := by
  apply hep_ext_empty
  · apply Derivor.ext (c := (unificationDerivor n sig).comp
      (heterogeneousDerivor (Fin (n + 1)) c))
      (d := (homogeneousDerivor (Fin n) c).comp (unificationDerivor n tau)) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base σ =>
      have h2 := Derivor.translate_comp (homogeneousInclusion (Fin n) tau)
        (unificationDerivor n tau) ((homogeneousInclusion (Fin n) tau).positionMap c.sortMap a)
        ((unificationDerivor n tau).positionMap c.sortMap _) (c.image σ)
      change Term.subst _ (heterogeneousTerm (Fin (n + 1)) (Fin.last n) (c.image σ)) = _
      refine (Derivor.subst_translate _ _ _ _).trans (Eq.trans ?_ h2)
      apply eq_of_heq
      apply Derivor.translate_heq (homogeneousInclusion_comp_unification n).symm
      apply heq_of_eq
      funext t x
      obtain ⟨j, h⟩ := x
      cases h
      apply eq_of_heq
      refine HEq.trans (heq_of_eq (Term.subst_var _ _)) ?_
      refine (valuation_heq _ _).trans ?_
      exact positionalTerm_heq _ _ _ _ rfl
    | source k s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) tau)
        (.identity (castSucc_lt_last k) _))
      funext j
      fin_cases j
      apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) tau)
        (.source (castSucc_lt_last k) _))
      funext j
      fin_cases j
      rfl
    | target k s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) tau)
        (.identity (castSucc_lt_last k) _))
      funext j
      fin_cases j
      apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) tau)
        (.target (castSucc_lt_last k) _))
      funext j
      fin_cases j
      rfl
    | comp k s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) tau)
        (.comp (castSucc_lt_last k) _))
      funext j
      fin_cases j <;> rfl
  · intro s
    change ⊥ ⊔ (heterogeneousDerivor (Fin (n + 1)) c).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]
  · intro s
    change ⊥ ⊔ (unificationDerivor n tau).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]

/-! ## Discretization and truncation -/

/-- Homogeneous discretization commutes with the derivors of a change of signature:
$\mathbf{c}^{(m)}\circ\mathbf{Ds}^{(n,m)}_{\Sigma}=\mathbf{Ds}^{(n,m)}_{\Lambda}\circ
\mathbf{c}^{(n)}$. -/
theorem homogeneousDiscretization_comp {m n : ℕ} (h : m ≤ n) (c : Derivor sig tau) :
    (homogeneousDiscretization sig h).comp (homogeneous (Fin m) c) =
      (homogeneous (Fin n) c).comp (homogeneousDiscretization tau h) := by
  apply hep_ext_empty
  · apply Derivor.ext (c := (homogeneousDiscretizationDerivor sig n m).comp
      (homogeneousDerivor (Fin m) c))
      (d := (homogeneousDerivor (Fin n) c).comp (homogeneousDiscretizationDerivor tau n m)) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base σ =>
      have h2 := Derivor.translate_comp (homogeneousInclusion (Fin n) tau)
        (homogeneousDiscretizationDerivor tau n m)
        ((homogeneousInclusion (Fin n) tau).positionMap c.sortMap a)
        ((homogeneousDiscretizationDerivor tau n m).positionMap c.sortMap _) (c.image σ)
      refine ((homogeneousDerivor (Fin m) c).translate_symbol (.base σ)).trans (Eq.trans ?_ h2)
      apply eq_of_heq
      apply Derivor.translate_heq (homogeneousInclusion_comp_discretization n m).symm
      apply heq_of_eq
      funext t x
      obtain ⟨j, h⟩ := x
      cases h
      rfl
    | source k s =>
      change (homogeneousDerivor (Fin m) c).translate _ (if hk : k.val < m then _ else _) =
        Term.substFamily _ (if hk : k.val < m then _ else _)
      by_cases hk : k.val < m
      · erw [dite_eq_left hk, dite_eq_left hk]
        apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin m) tau) (.source ⟨k.val, hk⟩ _))
        funext j
        fin_cases j
        rfl
      · erw [dite_eq_right hk, dite_eq_right hk]
        rfl
    | target k s =>
      change (homogeneousDerivor (Fin m) c).translate _ (if hk : k.val < m then _ else _) =
        Term.substFamily _ (if hk : k.val < m then _ else _)
      by_cases hk : k.val < m
      · erw [dite_eq_left hk, dite_eq_left hk]
        apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin m) tau) (.target ⟨k.val, hk⟩ _))
        funext j
        fin_cases j
        rfl
      · erw [dite_eq_right hk, dite_eq_right hk]
        rfl
    | comp k s =>
      change (homogeneousDerivor (Fin m) c).translate _ (if hk : k.val < m then _ else _) =
        Term.substFamily _ (if hk : k.val < m then _ else _)
      by_cases hk : k.val < m
      · erw [dite_eq_left hk, dite_eq_left hk]
        apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin m) tau) (.comp ⟨k.val, hk⟩ _))
        funext j
        fin_cases j <;> rfl
      · erw [dite_eq_right hk, dite_eq_right hk]
        rfl
  · intro s
    change ⊥ ⊔ (homogeneousDerivor (Fin m) c).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]
  · intro s
    change ⊥ ⊔ (homogeneousDiscretizationDerivor tau n m).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]

/-- Homogeneous truncation commutes with the derivors of a change of signature:
$\mathbf{c}^{(n)}\circ\mathbf{Tr}^{(m,n)}_{\Sigma}=\mathbf{Tr}^{(m,n)}_{\Lambda}\circ
\mathbf{c}^{(m)}$, domains included. -/
theorem homogeneousTruncation_comp {m n : ℕ} (h : m ≤ n) (c : Derivor sig tau) :
    (homogeneousTruncation sig h).comp (homogeneous (Fin n) c) =
      (homogeneous (Fin m) c).comp (homogeneousTruncation tau h) := by
  apply GeneralizedHepDerivor.ext
  · apply Derivor.ext (c := (homogeneousTruncationDerivor sig h).comp
      (homogeneousDerivor (Fin n) c))
      (d := (homogeneousDerivor (Fin m) c).comp (homogeneousTruncationDerivor tau h)) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base σ =>
      have h2 := Derivor.translate_comp (homogeneousInclusion (Fin m) tau)
        (homogeneousTruncationDerivor tau h)
        ((homogeneousInclusion (Fin m) tau).positionMap c.sortMap a)
        ((homogeneousTruncationDerivor tau h).positionMap c.sortMap _) (c.image σ)
      refine ((homogeneousDerivor (Fin n) c).translate_symbol (.base σ)).trans (Eq.trans ?_ h2)
      apply eq_of_heq
      apply Derivor.translate_heq (homogeneousInclusion_comp_truncation h).symm
      apply heq_of_eq
      funext t x
      obtain ⟨j, h⟩ := x
      cases h
      rfl
    | source k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau)
        (.source (dimensionInclusion h k) _))
      funext j
      fin_cases j
      rfl
    | target k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau)
        (.target (dimensionInclusion h k) _))
      funext j
      fin_cases j
      rfl
    | comp k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau)
        (.comp (dimensionInclusion h k) _))
      funext j
      fin_cases j <;> rfl
  · apply heq_of_eq
    funext s
    change ⊥ ⊔ (homogeneousDerivor (Fin n) c).translateSingletonSet _
        ((homogeneousTruncation sig h).domain s) =
      (homogeneousTruncation tau h).domain (c.sortMap s) ⊔
        (homogeneousTruncationDerivor tau h).translateSingletonSet _ ⊥
    erw [Derivor.translateSingletonSet_empty, sup_bot_eq, bot_sup_eq]
    by_cases hmn : m < n
    · unfold homogeneousTruncation
      simp only [dite_eq_left hmn]
      refine (translateSingletonSet_singleton (homogeneousDerivor (Fin n) c) _).trans ?_
      congr 1
      apply Prod.ext
      · rfl
      · apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau)
          (.source ⟨m, hmn⟩ _))
        funext j
        fin_cases j
        rfl
    · unfold homogeneousTruncation
      simp only [dite_eq_right hmn]
      exact Derivor.translateSingletonSet_empty _ _

/-- A monotone change of dimensions commutes with the heterogeneous derivors of a change of
signature. In particular heterogeneous discretization and truncation do, in finite
dimensions and in dimension $\omega$. -/
theorem heterogeneousDimension_comp {I : Type i} {J : Type j} [LinearOrder I]
    [LinearOrder J] (f : I →o J) (c : Derivor sig tau) :
    (heterogeneousDimension sig f).comp (heterogeneous J c) =
      (heterogeneous I c).comp (heterogeneousDimension tau f) := by
  apply hep_ext_empty
  · apply Derivor.ext (c := (heterogeneousDimensionDerivor sig f).comp
      (heterogeneousDerivor J c))
      (d := (heterogeneousDerivor I c).comp (heterogeneousDimensionDerivor tau f)) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base k σ =>
      have h2 := Derivor.translate_comp (heterogeneousInclusion I k tau)
        (heterogeneousDimensionDerivor tau f)
        (fun t x => .var (dimensionPosition k c.sortMap _ t x))
        ((heterogeneousDimensionDerivor tau f).positionMap (heterogeneousSortMap c) _)
        (c.image σ)
      change Term.subst _ (heterogeneousTerm J (f k) (c.image σ)) = _
      refine (Derivor.subst_translate _ _ _ _).trans (Eq.trans ?_ h2)
      apply eq_of_heq
      apply Derivor.translate_heq (heterogeneousInclusion_comp_dimension f k).symm
      apply heq_of_eq
      funext t x
      obtain ⟨j, h⟩ := x
      cases h
      apply eq_of_heq
      refine HEq.trans (heq_of_eq (Term.subst_var _ _)) ?_
      refine (valuation_heq _ _).trans ?_
      exact positionalTerm_heq _ _ _ _ rfl
    | @source j k h s =>
      change (heterogeneousDerivor J c).translate _ (if hh : f j < f k then _ else _) =
        Term.substFamily _ (if hh : f j < f k then _ else _)
      by_cases hh : f j < f k
      · erw [dite_eq_left hh, dite_eq_left hh]
        apply congrArg (Term.app (sig := Heterogeneous.Symbol J tau) (.source hh _))
        funext j
        fin_cases j
        rfl
      · erw [dite_eq_right hh, dite_eq_right hh]
        apply eq_of_heq
        unfold Term.substFamily
        refine HEq.trans ?_
          (HEq.trans (heq_of_eq (Term.subst_var _ _)) (valuation_heq _ _)).symm
        exact positionalTerm_heq _ _ _ _ rfl
    | @target j k h s =>
      change (heterogeneousDerivor J c).translate _ (if hh : f j < f k then _ else _) =
        Term.substFamily _ (if hh : f j < f k then _ else _)
      by_cases hh : f j < f k
      · erw [dite_eq_left hh, dite_eq_left hh]
        apply congrArg (Term.app (sig := Heterogeneous.Symbol J tau) (.target hh _))
        funext j
        fin_cases j
        rfl
      · erw [dite_eq_right hh, dite_eq_right hh]
        apply eq_of_heq
        unfold Term.substFamily
        refine HEq.trans ?_
          (HEq.trans (heq_of_eq (Term.subst_var _ _)) (valuation_heq _ _)).symm
        exact positionalTerm_heq _ _ _ _ rfl
    | @identity j k h s =>
      change (heterogeneousDerivor J c).translate _ (if hh : f j < f k then _ else _) =
        Term.substFamily _ (if hh : f j < f k then _ else _)
      by_cases hh : f j < f k
      · erw [dite_eq_left hh, dite_eq_left hh]
        apply congrArg (Term.app (sig := Heterogeneous.Symbol J tau) (.identity hh _))
        funext j
        fin_cases j
        rfl
      · erw [dite_eq_right hh, dite_eq_right hh]
        apply eq_of_heq
        unfold Term.substFamily
        refine HEq.trans ?_
          (HEq.trans (heq_of_eq (Term.subst_var _ _)) (valuation_heq _ _)).symm
        exact positionalTerm_heq _ _ _ _ rfl
    | @comp j k h s =>
      change (heterogeneousDerivor J c).translate _ (if hh : f j < f k then _ else _) =
        Term.substFamily _ (if hh : f j < f k then _ else _)
      by_cases hh : f j < f k
      · erw [dite_eq_left hh, dite_eq_left hh]
        apply congrArg (Term.app (sig := Heterogeneous.Symbol J tau) (.comp hh _))
        funext j
        fin_cases j <;> rfl
      · erw [dite_eq_right hh, dite_eq_right hh]
        apply eq_of_heq
        unfold Term.substFamily
        refine HEq.trans ?_
          (HEq.trans (heq_of_eq (Term.subst_var _ _)) (valuation_heq _ _)).symm
        exact positionalTerm_heq _ _ _ _ rfl
  · intro s
    change ⊥ ⊔ (heterogeneousDerivor J c).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]
  · intro s
    change ⊥ ⊔ (heterogeneousDimensionDerivor tau f).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]

end CategorialAlgebras.ChangeOfSignature
