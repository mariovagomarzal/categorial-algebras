import CategorialAlgebras.ChangeOfSignature.Omega
import CategorialAlgebras.Dimensions.OmegaFunctors

/-!
# Change of signature commutes with truncation and discretization in dimension $\omega$

The derivors of a change of signature commute with the truncation derivors from $\omega$
to $n$ and with the discretization derivors from $n$ to $\omega$, in both presentations:
$$\mathbf{c}^{(\omega)}\circ\mathbf{Tr}^{(n,\omega)}_{\Sigma}=\mathbf{Tr}^{(n,\omega)}_{\Lambda}
\circ\mathbf{c}^{(n)},\qquad
\mathbf{c}^{(n)}\circ\mathbf{Ds}^{(\omega,n)}_{\Sigma}=\mathbf{Ds}^{(\omega,n)}_{\Lambda}\circ
\mathbf{c}^{(\omega)},$$
and similarly in the heterogeneous presentation. Hence the functors commute:
$\mathrm{Tr}^{(n,\omega)}_{\Sigma}\circ\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Tr}^{(n,\omega)}_{\Lambda}$ and
$\mathrm{Ds}^{(\omega,n)}_{\Sigma}\circ\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}\circ\mathrm{Ds}^{(\omega,n)}_{\Lambda}$, by natural
isomorphisms that are identities on the underlying elements.

The homogeneous statements are proved once for every partial change of dimensions.
-/

universe i j u v w

namespace CategorialAlgebras.ChangeOfSignature

open CategoryTheory Presentations Dimensions

set_option backward.isDefEq.respectTransparency false

variable {S T : Type u} {sig : Signature.{u, v} S} {tau : Signature.{u, v} T}

/-! ## Partial changes of homogeneous dimensions -/

/-- A partial change of homogeneous dimensions fixes the terms of the base signature. -/
theorem homogeneousInclusion_comp_dimension {I : Type i} {J : Type j} (f : I → Option J) :
    (homogeneousInclusion I tau).comp (homogeneousDimensionDerivor tau f) =
      homogeneousInclusion J tau := by
  apply Derivor.ext (c := (homogeneousInclusion I tau).comp
    (homogeneousDimensionDerivor tau f)) (d := homogeneousInclusion J tau) rfl
  apply heq_of_eq
  funext a t τ
  rw [homogeneousInclusion_comp_image]
  rfl

/-- A partial change of homogeneous dimensions commutes with the homogeneous derivors of a
change of signature. -/
theorem homogeneousDimensionDerivor_comp {I : Type i} {J : Type j} (f : I → Option J)
    (c : Derivor sig tau) :
    (homogeneousDimensionDerivor sig f).comp (homogeneousDerivor J c) =
      (homogeneousDerivor I c).comp (homogeneousDimensionDerivor tau f) := by
  apply Derivor.ext (c := (homogeneousDimensionDerivor sig f).comp (homogeneousDerivor J c))
    (d := (homogeneousDerivor I c).comp (homogeneousDimensionDerivor tau f)) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base σ =>
    have h2 := Derivor.translate_comp (homogeneousInclusion I tau)
      (homogeneousDimensionDerivor tau f)
      ((homogeneousInclusion I tau).positionMap c.sortMap a)
      ((homogeneousDimensionDerivor tau f).positionMap c.sortMap _) (c.image σ)
    refine ((homogeneousDerivor J c).translate_symbol (.base σ)).trans (Eq.trans ?_ h2)
    apply eq_of_heq
    apply Derivor.translate_heq (homogeneousInclusion_comp_dimension f).symm
    apply heq_of_eq
    funext t x
    obtain ⟨j, h⟩ := x
    cases h
    rfl
  | source k s =>
    change (homogeneousDerivor J c).translate _ (match f k with
        | some j => Homogeneous.unary (.source j s) (.var (Word.position [s] 0))
        | none => .var (Word.position [s] 0)) =
      Term.substFamily _ (match f k with
        | some j => Homogeneous.unary (.source j (c.sortMap s))
            (.var (Word.position [c.sortMap s] 0))
        | none => .var (Word.position [c.sortMap s] 0))
    generalize f k = o
    cases o with
    | none => rfl
    | some j =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol J tau) (.source j _))
      funext q
      fin_cases q
      rfl
  | target k s =>
    change (homogeneousDerivor J c).translate _ (match f k with
        | some j => Homogeneous.unary (.target j s) (.var (Word.position [s] 0))
        | none => .var (Word.position [s] 0)) =
      Term.substFamily _ (match f k with
        | some j => Homogeneous.unary (.target j (c.sortMap s))
            (.var (Word.position [c.sortMap s] 0))
        | none => .var (Word.position [c.sortMap s] 0))
    generalize f k = o
    cases o with
    | none => rfl
    | some j =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol J tau) (.target j _))
      funext q
      fin_cases q
      rfl
  | comp k s =>
    change (homogeneousDerivor J c).translate _ (match f k with
        | some j => Homogeneous.binary j (.var (Word.position [s, s] 0))
            (.var (Word.position [s, s] 1))
        | none => .var (Word.position [s, s] 0)) =
      Term.substFamily _ (match f k with
        | some j => Homogeneous.binary j (.var (Word.position [c.sortMap s, c.sortMap s] 0))
            (.var (Word.position [c.sortMap s, c.sortMap s] 1))
        | none => .var (Word.position [c.sortMap s, c.sortMap s] 0))
    generalize f k = o
    cases o with
    | none => rfl
    | some j =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol J tau) (.comp j _))
      funext q
      fin_cases q <;> rfl

/-! ## The derivors in dimension $\omega$ -/

/-- The homogeneous derivor of a change of signature translates the $\omega$-dimensional
fixed-source equation of sort $s$ to that of sort $\varphi(s)$. -/
theorem homogeneous_translate_omegaEquation (n : ℕ) (c : Derivor sig tau) (s : S) :
    (homogeneousDerivor ℕ c).translateSingletonSet s
        (Homogeneous.singletonEquation (omegaTruncationEquation sig n s)) =
      Homogeneous.singletonEquation (omegaTruncationEquation tau n (c.sortMap s)) := by
  refine (translateSingletonSet_singleton (homogeneousDerivor ℕ c) _).trans ?_
  congr 1
  apply Prod.ext
  · rfl
  · apply congrArg (Term.app (sig := Homogeneous.Symbol ℕ tau) (.source n _))
    funext j
    fin_cases j
    rfl

/-- Homogeneous truncation from $\omega$ commutes with the derivors of a change of
signature, domains included. -/
theorem homogeneousOmegaTruncation_comp (n : ℕ) (c : Derivor sig tau) :
    (homogeneousOmegaTruncation sig n).comp (homogeneous ℕ c) =
      (homogeneous (Fin n) c).comp (homogeneousOmegaTruncation tau n) := by
  apply GeneralizedHepDerivor.ext (homogeneousDimensionDerivor_comp _ c)
  apply heq_of_eq
  funext s
  change ⊥ ⊔ (homogeneousDerivor ℕ c).translateSingletonSet _
      (Homogeneous.singletonEquation (omegaTruncationEquation sig n s)) =
    Homogeneous.singletonEquation (omegaTruncationEquation tau n (c.sortMap s)) ⊔
      (homogeneousOmegaTruncationDerivor tau n).translateSingletonSet _ ⊥
  erw [Derivor.translateSingletonSet_empty, sup_bot_eq, bot_sup_eq,
    homogeneous_translate_omegaEquation]

/-- Homogeneous discretization to $\omega$ commutes with the derivors of a change of
signature. -/
theorem homogeneousOmegaDiscretization_comp (n : ℕ) (c : Derivor sig tau) :
    (homogeneousOmegaDiscretization sig n).comp (homogeneous (Fin n) c) =
      (homogeneous ℕ c).comp (homogeneousOmegaDiscretization tau n) := by
  apply hep_ext_empty
  · change (homogeneousOmegaDiscretizationDerivor sig n).comp (homogeneousDerivor (Fin n) c) =
      (homogeneousDerivor ℕ c).comp (homogeneousOmegaDiscretizationDerivor tau n)
    rw [homogeneousOmegaDiscretizationDerivor_eq, homogeneousOmegaDiscretizationDerivor_eq]
    exact homogeneousDimensionDerivor_comp _ c
  · intro s
    change ⊥ ⊔ (homogeneousDerivor (Fin n) c).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]
  · intro s
    change ⊥ ⊔ (homogeneousOmegaDiscretizationDerivor tau n).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty, bot_sup_eq]

/-! ## Cells -/

/-- In a transformed $\omega$-dimensional model, the recovered boundaries of a cell of sort
$s$ are those of the original model at the sort $\varphi(s)$. -/
theorem homogeneous_omega_boundary_val (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ tau))
    (hB : (Homogeneous.specification ℕ tau).IsModel B)
    (k : ℕ) (b : Bool) (s : S) (x : (homogeneous ℕ c).Cell B s) :
    ((((omegaRecoveredAlgebra sig ((homogeneous ℕ c).transformed B)
        (homogeneous_isModel c B hB)).sort s).str.dim k).boundary b x).val =
      (((omegaRecoveredAlgebra tau B hB).sort (c.sortMap s)).str.dim k).boundary b x.val := by
  let hA := homogeneous_isModel c B hB
  let q := (((omegaRecoveredAlgebra sig ((homogeneous ℕ c).transformed B) hA).sort s).str.dim
    k).boundary b x
  have hq : q ∈ ((homogeneous ℕ c).transformed B).op
      (.boundary k s b) (Homogeneous.single x) := by
    cases b <;> erw [Homogeneous.boundary_op (fun e => hA.2 _ ⟨e, rfl⟩)] <;>
      exact Part.mem_some _
  have hv := ((homogeneous ℕ c).mem_transformed_op B _ _ _).mp hq |>.2
  cases b
  · change q.val ∈ Term.partialEval _ (Homogeneous.unary (.source k (c.sortMap s)) _) at hv
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some,
      Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ false] at hv
    exact Part.mem_some_iff.mp hv
  · change q.val ∈ Term.partialEval _ (Homogeneous.unary (.target k (c.sortMap s)) _) at hv
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some,
      Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ true] at hv
    exact Part.mem_some_iff.mp hv

/-- Truncation from $\omega$ followed by the homogeneous derivor of a change of signature
has a surjective canonical composition comparison on models. -/
theorem omegaTruncation_homogeneous_comparison_surjective (n : ℕ) (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ tau))
    (hB : (Homogeneous.specification ℕ tau).IsModel B) :
    ∀ s, Function.Surjective
      (((homogeneousOmegaTruncation sig n).comparison (homogeneous ℕ c) B).toMap s) := by
  apply ((homogeneousOmegaTruncation sig n).comparison_surjective_iff (homogeneous ℕ c) B).mpr
  intro s x hx
  change EEquationSet.Satisfies B _ ((homogeneousDerivor ℕ c).translateSingletonSet _
    (Homogeneous.singletonEquation (omegaTruncationEquation sig n s))) at hx
  rw [homogeneous_translate_omegaEquation] at hx
  apply (satisfies_omegaTruncationEquation_iff sig _ (homogeneous_isModel c B hB) n s x).mpr
  apply Subtype.ext
  exact (homogeneous_omega_boundary_val c B hB n false s x).trans
    ((satisfies_omegaTruncationEquation_iff tau B hB n (c.sortMap s) x.val).mp hx)

/-! ## The compatibility squares -/

/-- Homogeneous truncation from $\omega$ commutes with change of signature on all
$\omega$-dimensional models. -/
noncomputable def homogeneousOmegaTruncationAllModelsChange (n : ℕ) (c : Derivor sig tau) :
    homogeneousModels.{0, u, v, w} ℕ c ⋙ homogeneousOmegaTruncationAllModels sig n ≅
      homogeneousOmegaTruncationAllModels tau n ⋙ homogeneousModels (Fin n) c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor (homogeneousOmegaTruncation_comp n c))
    _ _ _ _ (homogeneousOmegaTruncation_isModel sig n) (homogeneous_isModel c)
    (homogeneous_isModel c) (homogeneousOmegaTruncation_isModel tau n)
    (fun B hB => omegaTruncation_homogeneous_comparison_surjective n c B hB)
    (fun B _ => (homogeneous (Fin n) c).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ p x => cells_of_eq (homogeneousOmegaTruncation_comp n c) B p x)

/-- Homogeneous truncation from $\omega$ commutes with change of signature on models. -/
noncomputable def homogeneousOmegaTruncationModelsChange (n : ℕ) (c : Derivor sig tau) :
    homogeneousOmegaModels.{u, v, w} c ⋙ homogeneousOmegaTruncationModels sig n ≅
      homogeneousOmegaTruncationModels tau n ⋙ homogeneousModels (Fin n) c :=
  Functor.isoWhiskerLeft (Homogeneous.omegaInclusion tau)
    (homogeneousOmegaTruncationAllModelsChange n c)

/-- Homogeneous discretization to $\omega$ commutes with change of signature on all
$\omega$-dimensional models. -/
noncomputable def homogeneousOmegaDiscretizationAllModelsChange (n : ℕ) (c : Derivor sig tau) :
    homogeneousModels.{0, u, v, w} (Fin n) c ⋙ homogeneousOmegaDiscretizationAllModels sig n ≅
      homogeneousOmegaDiscretizationAllModels tau n ⋙ homogeneousModels ℕ c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor (homogeneousOmegaDiscretization_comp n c))
    _ _ _ _ (homogeneousOmegaDiscretization_isModel sig n) (homogeneous_isModel c)
    (homogeneous_isModel c) (homogeneousOmegaDiscretization_isModel tau n)
    (fun B _ => (homogeneousOmegaDiscretization sig n).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ => (homogeneous ℕ c).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ p x => cells_of_eq (homogeneousOmegaDiscretization_comp n c) B p x)

/-- Homogeneous discretization to $\omega$ commutes with change of signature on models. -/
noncomputable def homogeneousOmegaDiscretizationModelsChange (n : ℕ) (c : Derivor sig tau) :
    homogeneousModels.{0, u, v, w} (Fin n) c ⋙ homogeneousOmegaDiscretizationModels sig n ≅
      homogeneousOmegaDiscretizationModels tau n ⋙ homogeneousOmegaModels c :=
  liftIso (homogeneousOmegaDiscretizationAllModelsChange n c)

/-- Heterogeneous truncation from $\omega$ commutes with change of signature on models. -/
noncomputable def heterogeneousOmegaTruncationModelsChange (n : ℕ) (c : Derivor sig tau) :
    heterogeneousModels.{0, u, v, w} ℕ c ⋙ heterogeneousOmegaTruncationModels sig n ≅
      heterogeneousOmegaTruncationModels tau n ⋙ heterogeneousModels (Fin (n + 1)) c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor
      (heterogeneousDimension_comp (omegaInclusion (n + 1)).toOrderHom c))
    _ _ _ _ (heterogeneousOmegaTruncation_isModel sig n) (heterogeneous_isModel c)
    (heterogeneous_isModel c) (heterogeneousOmegaTruncation_isModel tau n)
    (fun B _ => (heterogeneousOmegaTruncation sig n).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ => (heterogeneous (Fin (n + 1)) c).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ p x => cells_of_eq
      (heterogeneousDimension_comp (omegaInclusion (n + 1)).toOrderHom c) B p x)

/-- Heterogeneous discretization to $\omega$ commutes with change of signature on models. -/
noncomputable def heterogeneousOmegaDiscretizationModelsChange (n : ℕ) (c : Derivor sig tau) :
    heterogeneousModels.{0, u, v, w} (Fin (n + 1)) c ⋙
        heterogeneousOmegaDiscretizationModels sig n ≅
      heterogeneousOmegaDiscretizationModels tau n ⋙ heterogeneousModels ℕ c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor (heterogeneousDimension_comp (omegaClamp n) c))
    _ _ _ _ (heterogeneousOmegaDiscretization_isModel sig n) (heterogeneous_isModel c)
    (heterogeneous_isModel c) (heterogeneousOmegaDiscretization_isModel tau n)
    (fun B _ => (heterogeneousOmegaDiscretization sig n).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ => (heterogeneous ℕ c).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ p x => cells_of_eq (heterogeneousDimension_comp (omegaClamp n) c) B p x)

/-- Homogeneous truncation from $\omega$ commutes with change of signature:
$\mathrm{Tr}^{(n,\omega)}_{\Sigma}\circ\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Tr}^{(n,\omega)}_{\Lambda}$. -/
noncomputable def homogeneousOmegaTruncationFunctorChange (n : ℕ) (c : Derivor sig tau) :
    homogeneousOmegaFunctor.{u, v, w} c ⋙ homogeneousOmegaTruncationFunctor sig n ≅
      homogeneousOmegaTruncationFunctor tau n ⋙ homogeneousFunctor (Fin n) c :=
  conjugateSquareIso Homogeneous.omegaModelIsomorphism Homogeneous.omegaModelIsomorphism
    Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    (homogeneousOmegaTruncationModelsChange n c)

/-- Homogeneous discretization to $\omega$ commutes with change of signature:
$\mathrm{Ds}^{(\omega,n)}_{\Sigma}\circ\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}\circ\mathrm{Ds}^{(\omega,n)}_{\Lambda}$. -/
noncomputable def homogeneousOmegaDiscretizationFunctorChange (n : ℕ) (c : Derivor sig tau) :
    homogeneousFunctor.{0, u, v, w} (Fin n) c ⋙ homogeneousOmegaDiscretizationFunctor sig n ≅
      homogeneousOmegaDiscretizationFunctor tau n ⋙ homogeneousOmegaFunctor c :=
  conjugateSquareIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.omegaModelIsomorphism Homogeneous.omegaModelIsomorphism
    (homogeneousOmegaDiscretizationModelsChange n c)

/-- Heterogeneous truncation from $\omega$ commutes with change of signature:
$\mathrm{Tr}^{\mathrm{htg}(n,\omega)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(\omega)\ast}_{\mathfrak{gd}}
\cong\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}\circ
\mathrm{Tr}^{\mathrm{htg}(n,\omega)}_{\Lambda}$. -/
noncomputable def heterogeneousOmegaTruncationFunctorChange (n : ℕ) (c : Derivor sig tau) :
    heterogeneousFunctor.{0, u, v, w} ℕ c ⋙ heterogeneousOmegaTruncationFunctor sig n ≅
      heterogeneousOmegaTruncationFunctor tau n ⋙ heterogeneousFunctor (Fin (n + 1)) c :=
  conjugateSquareIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    (heterogeneousOmegaTruncationModelsChange n c)

/-- Heterogeneous discretization to $\omega$ commutes with change of signature:
$\mathrm{Ds}^{\mathrm{htg}(\omega,n)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}
\cong\mathbf{c}^{\mathrm{htg}(\omega)\ast}_{\mathfrak{gd}}\circ
\mathrm{Ds}^{\mathrm{htg}(\omega,n)}_{\Lambda}$. -/
noncomputable def heterogeneousOmegaDiscretizationFunctorChange (n : ℕ) (c : Derivor sig tau) :
    heterogeneousFunctor.{0, u, v, w} (Fin (n + 1)) c ⋙
        heterogeneousOmegaDiscretizationFunctor sig n ≅
      heterogeneousOmegaDiscretizationFunctor tau n ⋙ heterogeneousFunctor ℕ c :=
  conjugateSquareIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    (heterogeneousOmegaDiscretizationModelsChange n c)

/-! ## Naturality with respect to reducts -/

/-- Homogeneous truncation from $\omega$ is natural with respect to reducts. -/
noncomputable def homogeneousOmegaTruncationNaturality (n : ℕ) (c : Derivor sig tau) :
    homogeneousOmegaReductFunctor.{u, v, w} c ⋙ homogeneousOmegaTruncationFunctor sig n ≅ homogeneousOmegaTruncationFunctor tau n ⋙ homogeneousReductFunctor (Fin n) c :=
  Functor.isoWhiskerRight (homogeneousOmegaFunctorReductIso c).symm _ ≪≫ homogeneousOmegaTruncationFunctorChange n c ≪≫
    Functor.isoWhiskerLeft _ (homogeneousFunctorReductIso (Fin n) c)

/-- Homogeneous discretization to $\omega$ is natural with respect to reducts. -/
noncomputable def homogeneousOmegaDiscretizationNaturality (n : ℕ) (c : Derivor sig tau) :
    homogeneousReductFunctor.{0, u, u, v, v, w} (Fin n) c ⋙ homogeneousOmegaDiscretizationFunctor sig n ≅ homogeneousOmegaDiscretizationFunctor tau n ⋙ homogeneousOmegaReductFunctor c :=
  Functor.isoWhiskerRight (homogeneousFunctorReductIso (Fin n) c).symm _ ≪≫ homogeneousOmegaDiscretizationFunctorChange n c ≪≫
    Functor.isoWhiskerLeft _ (homogeneousOmegaFunctorReductIso c)

/-- Heterogeneous truncation from $\omega$ is natural with respect to reducts. -/
noncomputable def heterogeneousOmegaTruncationNaturality (n : ℕ) (c : Derivor sig tau) :
    heterogeneousReductFunctor.{0, u, u, v, v, w} ℕ c ⋙ heterogeneousOmegaTruncationFunctor sig n ≅ heterogeneousOmegaTruncationFunctor tau n ⋙ heterogeneousReductFunctor (Fin (n + 1)) c :=
  Functor.isoWhiskerRight (heterogeneousFunctorReductIso ℕ c).symm _ ≪≫ heterogeneousOmegaTruncationFunctorChange n c ≪≫
    Functor.isoWhiskerLeft _ (heterogeneousFunctorReductIso (Fin (n + 1)) c)

/-- Heterogeneous discretization to $\omega$ is natural with respect to reducts. -/
noncomputable def heterogeneousOmegaDiscretizationNaturality (n : ℕ) (c : Derivor sig tau) :
    heterogeneousReductFunctor.{0, u, u, v, v, w} (Fin (n + 1)) c ⋙ heterogeneousOmegaDiscretizationFunctor sig n ≅ heterogeneousOmegaDiscretizationFunctor tau n ⋙ heterogeneousReductFunctor ℕ c :=
  Functor.isoWhiskerRight (heterogeneousFunctorReductIso (Fin (n + 1)) c).symm _ ≪≫ heterogeneousOmegaDiscretizationFunctorChange n c ≪≫
    Functor.isoWhiskerLeft _ (heterogeneousFunctorReductIso ℕ c)

end CategorialAlgebras.ChangeOfSignature
