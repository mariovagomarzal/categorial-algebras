import CategorialAlgebras.Dimensions.OmegaFunctors
import CategorialAlgebras.Dimensions.Transport

/-!
# Composition with natural-dimensional truncations

Inclusions and clamps give the expected compositions. Homogeneous cell domains
are compared semantically: redundant cutoff equations select the same cells.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S : Type u} (sig : Signature.{u, v} S)

/-- Optional dimensions describe infinite homogeneous discretization. -/
theorem homogeneousOmegaDiscretizationDerivor_eq (n : ℕ) :
    homogeneousOmegaDiscretizationDerivor sig n = homogeneousDimensionDerivor sig
      (fun k : ℕ => if hk : k < n then some ⟨k, hk⟩ else none) := by
  apply Derivor.ext (c := homogeneousOmegaDiscretizationDerivor sig n)
    (d := homogeneousDimensionDerivor sig _) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base σ => rfl
  | source k s => dsimp [homogeneousOmegaDiscretizationDerivor, homogeneousDimensionDerivor]; split <;> rfl
  | target k s => dsimp [homogeneousOmegaDiscretizationDerivor, homogeneousDimensionDerivor]; split <;> rfl
  | comp k s => dsimp [homogeneousOmegaDiscretizationDerivor, homogeneousDimensionDerivor]; split <;> rfl

/-- Successive homogeneous inclusions retain the same operation symbols. -/
theorem homogeneousOmegaTruncation_comp_derivor {m n : ℕ} (h : m ≤ n) :
    (homogeneousTruncation sig h).toDerivor.comp
        (homogeneousOmegaTruncation sig n).toDerivor =
      (homogeneousOmegaTruncation sig m).toDerivor := by
  change (homogeneousTruncationDerivor sig h).comp
    (homogeneousDimensionDerivor sig (fun k : Fin n => some k.val)) =
      homogeneousDimensionDerivor sig (fun k : Fin m => some k.val)
  rw [homogeneousTruncationDerivor_eq, homogeneousDimensionDerivor_compose]
  rfl

/-- The upper mixed homogeneous composite retains the finite discretization terms. -/
theorem homogeneousOmegaMixed_upper_derivor {m n : ℕ} (h : m ≤ n) :
    (homogeneousOmegaTruncation sig n).toDerivor.comp
        (homogeneousOmegaDiscretization sig m).toDerivor =
      (homogeneousDiscretization sig h).toDerivor := by
  change (homogeneousDimensionDerivor sig _).comp
    (homogeneousOmegaDiscretizationDerivor sig m) = homogeneousDiscretizationDerivor sig n m
  rw [homogeneousOmegaDiscretizationDerivor_eq, homogeneousDiscretizationDerivor_eq,
    homogeneousDimensionDerivor_compose]
  rfl

/-- The lower mixed homogeneous composite retains the finite truncation terms. -/
theorem homogeneousOmegaMixed_lower_derivor {m n : ℕ} (h : n ≤ m) :
    (homogeneousOmegaTruncation sig n).toDerivor.comp
        (homogeneousOmegaDiscretization sig m).toDerivor =
      (homogeneousTruncation sig h).toDerivor := by
  change (homogeneousDimensionDerivor sig _).comp
    (homogeneousOmegaDiscretizationDerivor sig m) = homogeneousTruncationDerivor sig h
  rw [homogeneousOmegaDiscretizationDerivor_eq, homogeneousTruncationDerivor_eq,
    homogeneousDimensionDerivor_compose]
  congr 1
  funext k
  change (if hk : k.val < m then some (⟨k.val, hk⟩ : Fin m) else none) = _
  rw [dite_eq_left (lt_of_lt_of_le k.isLt h)]
  rfl

/-- Inclusion translates a finite cutoff equation to the corresponding natural dimension. -/
theorem omegaTruncation_translate_equation (n : ℕ) (k : Fin n) (s : S) :
    (homogeneousOmegaTruncationDerivor sig n).translateSingletonSet s
        (Homogeneous.singletonEquation (truncationEquation sig k s)) =
      Homogeneous.singletonEquation (omegaTruncationEquation sig k.val s) := by
  rw [translateSingletonSet_singleton]
  congr 1
  apply Prod.ext
  · rfl
  · change Term.app (sig := Homogeneous.Symbol ℕ sig) (.source k.val s) _ = _
    apply congrArg (Term.app (sig := Homogeneous.Symbol ℕ sig) (.source k.val s))
    funext q
    fin_cases q
    rfl

/-- Infinite discretization translates a retained cutoff equation to its finite source. -/
theorem omegaDiscretization_translate_equation_of_lt (m n : ℕ) (h : n < m) (s : S) :
    (homogeneousOmegaDiscretizationDerivor sig m).translateSingletonSet s
        (Homogeneous.singletonEquation (omegaTruncationEquation sig n s)) =
      Homogeneous.singletonEquation (truncationEquation sig ⟨n, h⟩ s) := by
  rw [translateSingletonSet_singleton]
  congr 1
  apply Prod.ext
  · rfl
  · change Term.substFamily _ (if hh : n < m then _ else _) = _
    erw [dite_eq_left h]
    change Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.source ⟨n, h⟩ s) _ = _
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin m) sig) (.source ⟨n, h⟩ s))
    funext q
    fin_cases q
    rfl

/-- A discarded natural-dimensional cutoff equation becomes reflexive. -/
theorem omegaDiscretization_translate_equation_of_le (m n : ℕ) (h : m ≤ n) (s : S) :
    (homogeneousOmegaDiscretizationDerivor sig m).translateSingletonSet s
        (Homogeneous.singletonEquation (omegaTruncationEquation sig n s)) =
      Homogeneous.singletonEquation (reflexiveEquation (n := m) sig s) := by
  rw [translateSingletonSet_singleton]
  congr 1
  apply Prod.ext
  · rfl
  · change Term.substFamily _ (if hh : n < m then _ else _) = _
    erw [dite_eq_right (not_lt_of_ge h)]
    rfl

/-- Below the initial dimension the mixed homogeneous hep-derivors are equal. -/
theorem homogeneousOmegaMixed_lower {m n : ℕ} (h : n < m) :
    (homogeneousOmegaTruncation sig n).comp (homogeneousOmegaDiscretization sig m) =
      homogeneousTruncation sig h.le := by
  apply GeneralizedHepDerivor.ext (homogeneousOmegaMixed_lower_derivor sig h.le)
  apply heq_of_eq
  funext s
  change ⊥ ⊔ (homogeneousOmegaDiscretizationDerivor sig m).translateSingletonSet s
    (Homogeneous.singletonEquation (omegaTruncationEquation sig n s)) = _
  erw [omegaDiscretization_translate_equation_of_lt sig m n h,
    bot_sup_eq, homogeneousTruncation_domain_of_lt sig h]

/-- Recover a natural-dimensional homogeneous model on its exact carrier. -/
noncomputable def omegaRecoveredAlgebra
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) :
    Homogeneous.CategorialAlgebra ℕ sig :=
  Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)

/-- A natural-dimensional fixed-source equation is equivalent to being a cutoff cell. -/
theorem satisfies_omegaTruncationEquation_iff
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) (n : ℕ) (s : S) (x : B.carrier s) :
    EEquationSet.Satisfies B (Word.singletonValuation x)
      (Homogeneous.singletonEquation (omegaTruncationEquation sig n s)) ↔
        ((omegaRecoveredAlgebra sig B hB).sort s).str.IsCell n x := by
  constructor
  · intro hx
    obtain ⟨q, hq, hr⟩ := hx s (omegaTruncationEquation sig n s) ⟨rfl, rfl⟩
    have he : q = x := Part.mem_some_iff.mp hq
    change q ∈ Term.partialEval _ (Homogeneous.boundary n false _) at hr
    erw [Homogeneous.eval_boundary (fun e => hB.2 _ ⟨e, rfl⟩), Term.partialEval_var,
      Part.bind_some] at hr
    exact (Part.mem_some_iff.mp hr).symm.trans he
  · intro hx t e ⟨ht, he⟩
    cases ht
    cases he
    refine ⟨x, Part.mem_some _, ?_⟩
    change x ∈ Term.partialEval (A := B) (Word.singletonValuation x)
      (Homogeneous.boundary n false (.var (Word.position _ 0)))
    erw [Homogeneous.eval_boundary (fun e => hB.2 _ ⟨e, rfl⟩), Term.partialEval_var,
      Part.bind_some]
    exact Part.mem_some_iff.mpr hx.symm

/-- The recovered source and target of a truncation have their original values. -/
theorem omegaTruncation_boundary_val (n : ℕ)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B)
    (k : Fin n) (b : Bool) (s : S) (x : (homogeneousOmegaTruncation sig n).Cell B s) :
    ((((recoveredAlgebra ((homogeneousOmegaTruncation sig n).transformed B)
        (homogeneousOmegaTruncation_isModel sig n B hB)).sort s).str.dim k).boundary b x).val =
      (((omegaRecoveredAlgebra sig B hB).sort s).str.dim k.val).boundary b x.val := by
  let hA := homogeneousOmegaTruncation_isModel sig n B hB
  let q := (((recoveredAlgebra ((homogeneousOmegaTruncation sig n).transformed B) hA).sort s).str.dim k).boundary b x
  have hq : q ∈ ((homogeneousOmegaTruncation sig n).transformed B).op
      (.boundary k s b) (Homogeneous.single x) := by
    cases b <;> erw [Homogeneous.boundary_op (fun e => hA.2 _ ⟨e, rfl⟩)] <;>
      exact Part.mem_some _
  have hv := ((homogeneousOmegaTruncation sig n).mem_transformed_op B _ _ _).mp hq |>.2
  cases b
  · change q.val ∈ Term.partialEval (A := B) _ (Homogeneous.unary (.source k.val s) _) at hv
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some,
      Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ false] at hv
    exact Part.mem_some_iff.mp hv
  · change q.val ∈ Term.partialEval (A := B) _ (Homogeneous.unary (.target k.val s) _) at hv
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some,
      Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ true] at hv
    exact Part.mem_some_iff.mp hv

/-- Successive truncations from natural dimensions select the same cells as the direct one. -/
theorem homogeneousOmegaTruncation_sameCells {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) (s : S) (x : B.carrier s) :
    ((homogeneousTruncation sig h).comp (homogeneousOmegaTruncation sig n)).IsCell B s x ↔
      (homogeneousOmegaTruncation sig m).IsCell B s x := by
  rcases h.lt_or_eq with h | rfl
  · change EEquationSet.Satisfies B _
      ((homogeneousOmegaTruncation sig n).domain s ⊔
        (homogeneousOmegaTruncationDerivor sig n).translateSingletonSet s
          ((homogeneousTruncation sig h.le).domain s)) ↔ _
    rw [homogeneousTruncation_domain_of_lt sig h, omegaTruncation_translate_equation]
    constructor
    · intro hx t e he
      exact hx t e (Or.inr he)
    · intro hx t e he
      rcases he with he | he
      · have hm := (satisfies_omegaTruncationEquation_iff sig B hB m s x).mp hx
        have hn := ((omegaRecoveredAlgebra sig B hB).sort s).str.isCell_mono h.le hm
        exact (satisfies_omegaTruncationEquation_iff sig B hB n s x).mpr hn t e he
      · exact hx t e he
  · have he : (homogeneousTruncation sig (le_refl m)).comp
        (homogeneousOmegaTruncation sig m) = homogeneousOmegaTruncation sig m := by
      rw [homogeneousTruncation_self, GeneralizedHepDerivor.identity_comp]
    have hd := congrFun (eq_of_heq (hepDomain_heq
      (c := (homogeneousTruncation sig (le_refl m)).comp (homogeneousOmegaTruncation sig m))
      (d := homogeneousOmegaTruncation sig m) he)) s
    change EEquationSet.Satisfies B _ _ ↔ _
    rw [hd]
    rfl

/-- The canonical comparison for a finite truncation after an infinite truncation is onto. -/
theorem homogeneousOmegaTruncation_comparison_surjective {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig))
    (hB : (Homogeneous.specification ℕ sig).IsModel B) :
    ∀ s, Function.Surjective
      (((homogeneousTruncation sig h).comparison (homogeneousOmegaTruncation sig n) B).toMap s) := by
  rcases h.lt_or_eq with h | rfl
  · apply ((homogeneousTruncation sig h.le).comparison_surjective_iff
      (homogeneousOmegaTruncation sig n) B).mpr
    intro s x hx
    change EEquationSet.Satisfies B _
      ((homogeneousOmegaTruncationDerivor sig n).translateSingletonSet s
        ((homogeneousTruncation sig h.le).domain s)) at hx
    rw [homogeneousTruncation_domain_of_lt sig h, omegaTruncation_translate_equation] at hx
    change EEquationSet.Satisfies _ _ ((homogeneousTruncation sig h.le).domain s)
    rw [homogeneousTruncation_domain_of_lt sig h]
    apply (satisfies_truncationEquation_iff _
      (homogeneousOmegaTruncation_isModel sig n B hB) ⟨m, h⟩ s x).mpr
    apply Subtype.ext
    exact (omegaTruncation_boundary_val sig n B hB ⟨m, h⟩ false s x).trans
      ((satisfies_omegaTruncationEquation_iff sig B hB m s x.val).mp hx)
  · exact (homogeneousTruncation sig (le_refl m)).comparison_surjective_of_empty
      (homogeneousOmegaTruncation sig m) B (homogeneousTruncation_domain_self sig m)
/-- Discretization retains lower recovered boundaries and makes higher ones identities. -/
theorem omegaDiscretization_boundary_val (m : ℕ)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (hB : (Homogeneous.specification (Fin m) sig).IsModel B)
    (k : ℕ) (b : Bool) (s : S) (x : (homogeneousOmegaDiscretization sig m).Cell B s) :
    ((((omegaRecoveredAlgebra sig ((homogeneousOmegaDiscretization sig m).transformed B)
        (homogeneousOmegaDiscretization_isModel sig m B hB)).sort s).str.dim k).boundary b x).val =
      if hk : k < m then
        (((recoveredAlgebra B hB).sort s).str.dim ⟨k, hk⟩).boundary b x.val else x.val := by
  let hA := homogeneousOmegaDiscretization_isModel sig m B hB
  let q := (((omegaRecoveredAlgebra sig ((homogeneousOmegaDiscretization sig m).transformed B) hA).sort s).str.dim k).boundary b x
  have hq : q ∈ ((homogeneousOmegaDiscretization sig m).transformed B).op
      (.boundary k s b) (Homogeneous.single x) := by
    cases b <;> erw [Homogeneous.boundary_op (fun e => hA.2 _ ⟨e, rfl⟩)] <;>
      exact Part.mem_some _
  have hv := ((homogeneousOmegaDiscretization sig m).mem_transformed_op B _ _ _).mp hq |>.2
  cases b
  · change q.val ∈ Term.partialEval (A := B)
      (Word.valuation (φ := id) (fun j => (Homogeneous.single x j).val))
      (if hk : k < m then Homogeneous.unary (.source ⟨k, hk⟩ s)
        (.var (Word.position _ 0)) else .var (Word.position _ 0)) at hv
    by_cases hk : k < m
    · erw [dite_eq_left hk, Homogeneous.partialEval_unary, Term.partialEval_var,
        Part.bind_some, Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ false] at hv
      erw [dite_eq_left hk]
      exact Part.mem_some_iff.mp hv
    · erw [dite_eq_right hk, Term.partialEval_var] at hv
      erw [dite_eq_right hk]
      exact Part.mem_some_iff.mp hv
  · change q.val ∈ Term.partialEval (A := B)
      (Word.valuation (φ := id) (fun j => (Homogeneous.single x j).val))
      (if hk : k < m then Homogeneous.unary (.target ⟨k, hk⟩ s)
        (.var (Word.position _ 0)) else .var (Word.position _ 0)) at hv
    by_cases hk : k < m
    · erw [dite_eq_left hk, Homogeneous.partialEval_unary, Term.partialEval_var,
        Part.bind_some, Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ true] at hv
      erw [dite_eq_left hk]
      exact Part.mem_some_iff.mp hv
    · erw [dite_eq_right hk, Term.partialEval_var] at hv
      erw [dite_eq_right hk]
      exact Part.mem_some_iff.mp hv


/-- The upper mixed homogeneous domain is satisfied by every element. -/
theorem homogeneousOmegaMixed_upper_isCell {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (s : S) (x : B.carrier s) :
    ((homogeneousOmegaTruncation sig n).comp (homogeneousOmegaDiscretization sig m)).IsCell B s x := by
  change EEquationSet.Satisfies B _
    (⊥ ⊔ (homogeneousOmegaDiscretizationDerivor sig m).translateSingletonSet s
      (Homogeneous.singletonEquation (omegaTruncationEquation sig n s)))
  erw [omegaDiscretization_translate_equation_of_le sig m n h, bot_sup_eq]
  exact satisfies_reflexiveEquation B s x

/-- The lower mixed homogeneous composite selects the same cells as finite truncation. -/
theorem homogeneousOmegaMixed_lower_sameCells {m n : ℕ} (h : n ≤ m)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (s : S) (x : B.carrier s) :
    ((homogeneousOmegaTruncation sig n).comp (homogeneousOmegaDiscretization sig m)).IsCell B s x ↔
      (homogeneousTruncation sig h).IsCell B s x := by
  rcases h.lt_or_eq with h | rfl
  · exact cells_of_eq (homogeneousOmegaMixed_lower sig h) B s x
  · exact ⟨fun _ => (homogeneousTruncation sig (le_refl n)).isCell_of_empty
      (homogeneousTruncation_domain_self sig n) B s x,
      fun _ => homogeneousOmegaMixed_upper_isCell sig (le_refl n) B s x⟩

/-- Mixed homogeneous comparisons reflect the cutoff equation on every finite model. -/
theorem homogeneousOmegaMixed_comparison_surjective (m n : ℕ)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (hB : (Homogeneous.specification (Fin m) sig).IsModel B) :
    ∀ s, Function.Surjective
      (((homogeneousOmegaTruncation sig n).comparison (homogeneousOmegaDiscretization sig m) B).toMap s) := by
  apply ((homogeneousOmegaTruncation sig n).comparison_surjective_iff
    (homogeneousOmegaDiscretization sig m) B).mpr
  intro s x hx
  apply (satisfies_omegaTruncationEquation_iff sig _
    (homogeneousOmegaDiscretization_isModel sig m B hB) n s x).mpr
  apply Subtype.ext
  have hv := omegaDiscretization_boundary_val sig m B hB n false s x
  by_cases hn : n < m
  · change EEquationSet.Satisfies B _
      ((homogeneousOmegaDiscretizationDerivor sig m).translateSingletonSet s
        (Homogeneous.singletonEquation (omegaTruncationEquation sig n s))) at hx
    rw [omegaDiscretization_translate_equation_of_lt sig m n hn] at hx
    erw [dite_eq_left hn] at hv
    exact hv.trans ((satisfies_truncationEquation_iff B hB ⟨n, hn⟩ s x.val).mp hx)
  · erw [dite_eq_right hn] at hv
    exact hv

/-- Natural-dimensional homogeneous truncation followed by finite truncation
is naturally the direct truncation on all models. -/
noncomputable def homogeneousOmegaTruncationAllModelsComp {m n : ℕ} (h : m ≤ n) :
    homogeneousOmegaTruncationAllModels.{u, v, w} sig n ⋙ homogeneousTruncationModels sig h ≅
      homogeneousOmegaTruncationAllModels sig m :=
  inducedCompositeModelsNatIso _ _ _ (homogeneousOmegaTruncation_comp_derivor sig h) _ _ _
    (homogeneousTruncation_isModel sig h) (homogeneousOmegaTruncation_isModel sig n)
    (homogeneousOmegaTruncation_isModel sig m)
    (homogeneousOmegaTruncation_comparison_surjective sig h)
    (fun B hB s x => homogeneousOmegaTruncation_sameCells sig h B hB s x)

/-- The homogeneous infinite truncations form a cone up to canonical isomorphism. -/
noncomputable def homogeneousOmegaTruncationModelsComp {m n : ℕ} (h : m ≤ n) :
    homogeneousOmegaTruncationModels.{u, v, w} sig n ⋙ homogeneousTruncationModels sig h ≅
      homogeneousOmegaTruncationModels sig m :=
  Functor.isoWhiskerLeft (Homogeneous.omegaInclusion sig)
    (homogeneousOmegaTruncationAllModelsComp sig h)

/-- Truncation above the initial homogeneous dimension gives finite discretization. -/
noncomputable def homogeneousOmegaMixedUpperModels {m n : ℕ} (h : m ≤ n) :
    homogeneousOmegaDiscretizationModels.{u, v, w} sig m ⋙
      homogeneousOmegaTruncationModels sig n ≅ homogeneousDiscretizationModels sig h :=
  inducedCompositeModelsNatIso _ _ _ (homogeneousOmegaMixed_upper_derivor sig h) _ _ _
    (homogeneousOmegaTruncation_isModel sig n) (homogeneousOmegaDiscretization_isModel sig m)
    (homogeneousDiscretization_isModel sig h) (homogeneousOmegaMixed_comparison_surjective sig m n)
    (fun B _ s x => ⟨fun _ => homogeneousDiscretization_isCell sig h B s x,
      fun _ => homogeneousOmegaMixed_upper_isCell sig h B s x⟩)

/-- Truncation below the initial homogeneous dimension gives finite truncation. -/
noncomputable def homogeneousOmegaMixedLowerModels {m n : ℕ} (h : n ≤ m) :
    homogeneousOmegaDiscretizationModels.{u, v, w} sig m ⋙
      homogeneousOmegaTruncationModels sig n ≅ homogeneousTruncationModels sig h :=
  inducedCompositeModelsNatIso _ _ _ (homogeneousOmegaMixed_lower_derivor sig h) _ _ _
    (homogeneousOmegaTruncation_isModel sig n) (homogeneousOmegaDiscretization_isModel sig m)
    (homogeneousTruncation_isModel sig h) (homogeneousOmegaMixed_comparison_surjective sig m n)
    (fun B _ s x => homogeneousOmegaMixed_lower_sameCells sig h B s x)

/-- The heterogeneous infinite truncations form a cone up to canonical isomorphism. -/
noncomputable def heterogeneousOmegaTruncationModelsComp {m n : ℕ} (h : m ≤ n) :
    heterogeneousOmegaTruncationModels.{u, v, w} sig n ⋙ heterogeneousTruncationModels sig h ≅
      heterogeneousOmegaTruncationModels sig m :=
  inducedCompositeModelsNatIsoOfEq _ _ _ _ _ _
    (heterogeneousTruncation_isModel sig h) (heterogeneousOmegaTruncation_isModel sig n)
    (heterogeneousOmegaTruncation_isModel sig m)
    (fun B _ => (heterogeneousTruncation sig h).comparison_surjective_of_empty _ B (fun _ => rfl))
    (heterogeneousOmegaTruncation_comp sig h)

/-- Truncation above the initial heterogeneous dimension gives finite discretization. -/
noncomputable def heterogeneousOmegaMixedUpperModels {m n : ℕ} (h : m ≤ n) :
    heterogeneousOmegaDiscretizationModels.{u, v, w} sig m ⋙
      heterogeneousOmegaTruncationModels sig n ≅ heterogeneousDiscretizationModels sig h :=
  inducedCompositeModelsNatIsoOfEq _ _ _ _ _ _
    (heterogeneousOmegaTruncation_isModel sig n) (heterogeneousOmegaDiscretization_isModel sig m)
    (heterogeneousDiscretization_isModel sig h)
    (fun B _ => (heterogeneousOmegaTruncation sig n).comparison_surjective_of_empty _ B (fun _ => rfl))
    (heterogeneousOmegaMixed_upper sig h)

/-- Truncation below the initial heterogeneous dimension gives finite truncation. -/
noncomputable def heterogeneousOmegaMixedLowerModels {m n : ℕ} (h : n ≤ m) :
    heterogeneousOmegaDiscretizationModels.{u, v, w} sig m ⋙
      heterogeneousOmegaTruncationModels sig n ≅ heterogeneousTruncationModels sig h :=
  inducedCompositeModelsNatIsoOfEq _ _ _ _ _ _
    (heterogeneousOmegaTruncation_isModel sig n) (heterogeneousOmegaDiscretization_isModel sig m)
    (heterogeneousTruncation_isModel sig h)
    (fun B _ => (heterogeneousOmegaTruncation sig n).comparison_surjective_of_empty _ B (fun _ => rfl))
    (heterogeneousOmegaMixed_lower sig h)

/-- Homogeneous truncations from $\omega$ compose by the canonical elementwise identification. -/
noncomputable def homogeneousOmegaTruncationFunctorComp {m n : ℕ} (h : m ≤ n) :
    homogeneousOmegaTruncationFunctor.{u, v, w} sig n ⋙ homogeneousTruncationFunctor sig h ≅
      homogeneousOmegaTruncationFunctor sig m :=
  conjugateCompositeIso Homogeneous.omegaModelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousOmegaTruncationModelsComp sig h)

/-- Heterogeneous truncations from $\omega$ compose by the canonical elementwise identification. -/
noncomputable def heterogeneousOmegaTruncationFunctorComp {m n : ℕ} (h : m ≤ n) :
    heterogeneousOmegaTruncationFunctor.{u, v, w} sig n ⋙ heterogeneousTruncationFunctor sig h ≅
      heterogeneousOmegaTruncationFunctor sig m :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousOmegaTruncationModelsComp sig h)

/-- Homogeneous discretization followed by truncation above the initial dimension. -/
noncomputable def homogeneousOmegaMixedUpperFunctor {m n : ℕ} (h : m ≤ n) :
    homogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⋙ homogeneousOmegaTruncationFunctor sig n ≅
      homogeneousDiscretizationFunctor sig h :=
  conjugateCompositeIso Homogeneous.modelIsomorphism Homogeneous.omegaModelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousOmegaMixedUpperModels sig h)

/-- Homogeneous discretization followed by truncation below the initial dimension. -/
noncomputable def homogeneousOmegaMixedLowerFunctor {m n : ℕ} (h : n ≤ m) :
    homogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⋙ homogeneousOmegaTruncationFunctor sig n ≅
      homogeneousTruncationFunctor sig h :=
  conjugateCompositeIso Homogeneous.modelIsomorphism Homogeneous.omegaModelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousOmegaMixedLowerModels sig h)

/-- Heterogeneous discretization followed by truncation above the initial dimension. -/
noncomputable def heterogeneousOmegaMixedUpperFunctor {m n : ℕ} (h : m ≤ n) :
    heterogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⋙ heterogeneousOmegaTruncationFunctor sig n ≅
      heterogeneousDiscretizationFunctor sig h :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousOmegaMixedUpperModels sig h)

/-- Heterogeneous discretization followed by truncation below the initial dimension. -/
noncomputable def heterogeneousOmegaMixedLowerFunctor {m n : ℕ} (h : n ≤ m) :
    heterogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⋙ heterogeneousOmegaTruncationFunctor sig n ≅
      heterogeneousTruncationFunctor sig h :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousOmegaMixedLowerModels sig h)

set_option backward.isDefEq.respectTransparency false

/-- The mixed homogeneous comparison retains the underlying element. -/
theorem homogeneousOmegaMixedUpperModels_hom_val {m n : ℕ} (h : m ≤ n)
    (B : (Homogeneous.specification (Fin m) sig).Models) (s) (x) :
    (((homogeneousOmegaMixedUpperModels.{u, v, w} sig h).hom.app B).hom.hom.toMap s x).val = x.val.val := by
  exact eq_of_heq (inducedCompositeModelsNatIso_hom_heq
    (homogeneousOmegaTruncation sig n) (homogeneousOmegaDiscretization sig m) (homogeneousDiscretization sig h) (homogeneousOmegaMixed_upper_derivor sig h)
    (Homogeneous.specification (Fin n) sig) (Homogeneous.specification ℕ sig) (Homogeneous.specification (Fin m) sig)
    (homogeneousOmegaTruncation_isModel sig n) (homogeneousOmegaDiscretization_isModel sig m) (homogeneousDiscretization_isModel sig h)
    (homogeneousOmegaMixed_comparison_surjective sig m n) (fun B _ s x => ⟨fun _ => homogeneousDiscretization_isCell sig h B s x,
      fun _ => homogeneousOmegaMixed_upper_isCell sig h B s x⟩) B s x)

/-- The mixed homogeneous comparison retains the underlying element. -/
theorem homogeneousOmegaMixedLowerModels_hom_val {m n : ℕ} (h : n ≤ m)
    (B : (Homogeneous.specification (Fin m) sig).Models) (s) (x) :
    (((homogeneousOmegaMixedLowerModels.{u, v, w} sig h).hom.app B).hom.hom.toMap s x).val = x.val.val := by
  exact eq_of_heq (inducedCompositeModelsNatIso_hom_heq
    (homogeneousOmegaTruncation sig n) (homogeneousOmegaDiscretization sig m) (homogeneousTruncation sig h) (homogeneousOmegaMixed_lower_derivor sig h)
    (Homogeneous.specification (Fin n) sig) (Homogeneous.specification ℕ sig) (Homogeneous.specification (Fin m) sig)
    (homogeneousOmegaTruncation_isModel sig n) (homogeneousOmegaDiscretization_isModel sig m) (homogeneousTruncation_isModel sig h)
    (homogeneousOmegaMixed_comparison_surjective sig m n) (fun B _ s x => homogeneousOmegaMixed_lower_sameCells sig h B s x) B s x)

/-- The mixed heterogeneous comparison retains the underlying element. -/
theorem heterogeneousOmegaMixedUpperModels_hom_heq {m n : ℕ} (h : m ≤ n)
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) (s) (x) :
    HEq ((((heterogeneousOmegaMixedUpperModels.{u, v, w} sig h).hom.app B).hom.hom.toMap s x).val) x.val.val := by
  exact inducedCompositeModelsNatIso_hom_heq
    (heterogeneousOmegaTruncation sig n) (heterogeneousOmegaDiscretization sig m) (heterogeneousDiscretization sig h) (congrArg GeneralizedHepDerivor.toDerivor (heterogeneousOmegaMixed_upper sig h))
    (Heterogeneous.specification (Fin (n + 1)) sig) (Heterogeneous.specification ℕ sig) (Heterogeneous.specification (Fin (m + 1)) sig)
    (heterogeneousOmegaTruncation_isModel sig n) (heterogeneousOmegaDiscretization_isModel sig m) (heterogeneousDiscretization_isModel sig h)
    (fun B _ => (heterogeneousOmegaTruncation sig n).comparison_surjective_of_empty _ B (fun _ => rfl)) (fun B _ s x => cells_of_eq (heterogeneousOmegaMixed_upper sig h) B s x) B s x

/-- The mixed heterogeneous comparison retains the underlying element. -/
theorem heterogeneousOmegaMixedLowerModels_hom_heq {m n : ℕ} (h : n ≤ m)
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) (s) (x) :
    HEq ((((heterogeneousOmegaMixedLowerModels.{u, v, w} sig h).hom.app B).hom.hom.toMap s x).val) x.val.val := by
  exact inducedCompositeModelsNatIso_hom_heq
    (heterogeneousOmegaTruncation sig n) (heterogeneousOmegaDiscretization sig m) (heterogeneousTruncation sig h) (congrArg GeneralizedHepDerivor.toDerivor (heterogeneousOmegaMixed_lower sig h))
    (Heterogeneous.specification (Fin (n + 1)) sig) (Heterogeneous.specification ℕ sig) (Heterogeneous.specification (Fin (m + 1)) sig)
    (heterogeneousOmegaTruncation_isModel sig n) (heterogeneousOmegaDiscretization_isModel sig m) (heterogeneousTruncation_isModel sig h)
    (fun B _ => (heterogeneousOmegaTruncation sig n).comparison_surjective_of_empty _ B (fun _ => rfl)) (fun B _ s x => cells_of_eq (heterogeneousOmegaMixed_lower sig h) B s x) B s x

end CategorialAlgebras.Dimensions
