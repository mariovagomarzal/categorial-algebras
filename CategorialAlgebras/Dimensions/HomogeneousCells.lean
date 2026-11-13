import CategorialAlgebras.Dimensions.HomogeneousDomains

/-!
# Homogeneous cell comparisons

Fixed-source equations characterize the selected cells. The total boundaries
of transformed models retain their original values below the cutoff and become
identities above it. These formulas reflect the translated cell equations.
-/

universe u v w

namespace CategorialAlgebras.Homogeneous

/-- Select source or target of a homogeneous category structure. -/
def CategoryStructure.boundary {A : Type w} (C : CategoryStructure A) (b : Bool) : A → A :=
  if b then C.target else C.source

end CategorialAlgebras.Homogeneous

namespace CategorialAlgebras.Dimensions

open Presentations

variable {S : Type u} {sig : Signature.{u, v} S}

/-- Recover the homogeneous algebra of a model, retaining its exact carrier. -/
noncomputable def recoveredAlgebra {n : ℕ}
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    Homogeneous.NCategorialAlgebra n sig :=
  Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)

/-- Satisfaction of a fixed-source singleton means that the recovered source fixes the element. -/
theorem satisfies_truncationEquation_iff {n : ℕ}
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B)
    (k : Fin n) (s : S) (x : B.carrier s) :
    EEquationSet.Satisfies B (Word.singletonValuation x)
        (Homogeneous.singletonEquation (truncationEquation sig k s)) ↔
      ((recoveredAlgebra B hB).sort s).str.IsCell k x := by
  constructor
  · intro hx
    obtain ⟨q, hq, hr⟩ := hx s (truncationEquation sig k s) ⟨rfl, rfl⟩
    have he : q = x := Part.mem_some_iff.mp hq
    change q ∈ Term.partialEval _ (Homogeneous.boundary k false _) at hr
    erw [Homogeneous.eval_boundary (fun e => hB.2 _ ⟨e, rfl⟩), Term.partialEval_var,
      Part.bind_some] at hr
    exact (Part.mem_some_iff.mp hr).symm.trans he
  · intro hx t e ⟨ht, he⟩
    cases ht
    cases he
    refine ⟨x, Part.mem_some _, ?_⟩
    change x ∈ Term.partialEval _ (Homogeneous.boundary k false _)
    erw [Homogeneous.eval_boundary (fun e => hB.2 _ ⟨e, rfl⟩), Term.partialEval_var,
      Part.bind_some]
    exact Part.mem_some_iff.mpr hx.symm

/-- A reflexive existence domain is satisfied by every element of any partial algebra. -/
theorem satisfies_reflexiveEquation {n : ℕ}
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (s : S) (x : B.carrier s) :
    EEquationSet.Satisfies B (Word.singletonValuation x)
      (Homogeneous.singletonEquation (reflexiveEquation sig s)) := by
  intro t e ⟨ht, he⟩
  cases ht
  cases he
  exact ⟨x, Part.mem_some _, Part.mem_some _⟩

/-- In an arbitrary model, truncation selects exactly the finite cells at its cutoff. -/
theorem homogeneousTruncation_isCell_iff_model {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) (s : S) (x : B.carrier s) :
    (homogeneousTruncation sig h).IsCell B s x ↔
      IsFiniteCell ((recoveredAlgebra B hB).sort s).str (cellInclusion h (Fin.last m)) x := by
  rcases h.lt_or_eq with hm | rfl
  · change EEquationSet.Satisfies B (Word.singletonValuation x)
      (if hh : m < n then _ else _) ↔ _
    erw [dite_eq_left hm]
    exact (satisfies_truncationEquation_iff B hB ⟨m, hm⟩ s x).trans
      ⟨fun hx _ => hx, fun hx => hx hm⟩
  · change EEquationSet.Satisfies B (Word.singletonValuation x)
      ((homogeneousTruncation sig h).domain s) ↔ _
    rw [homogeneousTruncation_domain_self]
    exact ⟨fun _ => isFiniteCell_last _ _, fun _ _ _ he => he.elim⟩

/-- Truncation restricts each recovered total boundary to the selected subtype. -/
theorem truncation_boundary_val {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B)
    (k : Fin m) (b : Bool) (s : S) (x : (homogeneousTruncation sig h).Cell B s) :
    ((((recoveredAlgebra ((homogeneousTruncation sig h).transformed B)
        (homogeneousTruncation_isModel sig h B hB)).sort s).str.dim k).boundary b x).val =
      (((recoveredAlgebra B hB).sort s).str.dim (dimensionInclusion h k)).boundary b x.val := by
  let hA := homogeneousTruncation_isModel sig h B hB
  let q := (((recoveredAlgebra ((homogeneousTruncation sig h).transformed B) hA).sort s).str.dim k).boundary b x
  have hq : q ∈ ((homogeneousTruncation sig h).transformed B).op
      (.boundary k s b) (Homogeneous.single x) := by
    cases b <;> erw [Homogeneous.boundary_op (fun e => hA.2 _ ⟨e, rfl⟩)] <;>
      exact Part.mem_some _
  have hv := ((homogeneousTruncation sig h).mem_transformed_op B _ _ _).mp hq |>.2
  cases b
  · change q.val ∈ Term.partialEval _ (Homogeneous.unary (.source (dimensionInclusion h k) s) _) at hv
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some,
      Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ false] at hv
    exact Part.mem_some_iff.mp hv
  · change q.val ∈ Term.partialEval _ (Homogeneous.unary (.target (dimensionInclusion h k) s) _) at hv
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some,
      Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ true] at hv
    exact Part.mem_some_iff.mp hv

/-- Discretization retains lower recovered boundaries and makes higher ones identities. -/
theorem discretization_boundary_val {m n : ℕ} (h : m ≤ n)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (hB : (Homogeneous.specification (Fin m) sig).IsModel B)
    (k : Fin n) (b : Bool) (s : S) (x : (homogeneousDiscretization sig h).Cell B s) :
    ((((recoveredAlgebra ((homogeneousDiscretization sig h).transformed B)
        (homogeneousDiscretization_isModel sig h B hB)).sort s).str.dim k).boundary b x).val =
      if hk : k.val < m then
        (((recoveredAlgebra B hB).sort s).str.dim ⟨k.val, hk⟩).boundary b x.val else x.val := by
  let hA := homogeneousDiscretization_isModel sig h B hB
  let q := (((recoveredAlgebra ((homogeneousDiscretization sig h).transformed B) hA).sort s).str.dim k).boundary b x
  have hq : q ∈ ((homogeneousDiscretization sig h).transformed B).op
      (.boundary k s b) (Homogeneous.single x) := by
    cases b <;> erw [Homogeneous.boundary_op (fun e => hA.2 _ ⟨e, rfl⟩)] <;>
      exact Part.mem_some _
  have hv := ((homogeneousDiscretization sig h).mem_transformed_op B _ _ _).mp hq |>.2
  cases b
  · change q.val ∈ Term.partialEval (A := B)
      (Word.valuation (φ := id) (fun j => (Homogeneous.single x j).val))
      (if hk : k.val < m then Homogeneous.unary (.source ⟨k.val, hk⟩ s)
        (.var (Word.position _ 0)) else .var (Word.position _ 0)) at hv
    by_cases hk : k.val < m
    · erw [dite_eq_left hk, Homogeneous.partialEval_unary, Term.partialEval_var,
        Part.bind_some, Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ false] at hv
      erw [dite_eq_left hk]
      exact Part.mem_some_iff.mp hv
    · erw [dite_eq_right hk, Term.partialEval_var] at hv
      erw [dite_eq_right hk]
      exact Part.mem_some_iff.mp hv
  · change q.val ∈ Term.partialEval (A := B)
      (Word.valuation (φ := id) (fun j => (Homogeneous.single x j).val))
      (if hk : k.val < m then Homogeneous.unary (.target ⟨k.val, hk⟩ s)
        (.var (Word.position _ 0)) else .var (Word.position _ 0)) at hv
    by_cases hk : k.val < m
    · erw [dite_eq_left hk, Homogeneous.partialEval_unary, Term.partialEval_var,
        Part.bind_some, Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ true] at hv
      erw [dite_eq_left hk]
      exact Part.mem_some_iff.mp hv
    · erw [dite_eq_right hk, Term.partialEval_var] at hv
      erw [dite_eq_right hk]
      exact Part.mem_some_iff.mp hv


/-- Successive homogeneous truncations select exactly the cells selected by the direct truncation. -/
theorem homogeneousTruncation_comp_sameCells {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin p) sig))
    (hB : (Homogeneous.specification (Fin p) sig).IsModel B) (s : S) (x : B.carrier s) :
    ((homogeneousTruncation sig hmn).comp (homogeneousTruncation sig hnp)).IsCell B s x ↔
      (homogeneousTruncation sig (le_trans hmn hnp)).IsCell B s x := by
  rcases hmn.lt_or_eq with hm | rfl
  · rcases hnp.lt_or_eq with hn | rfl
    · change EEquationSet.Satisfies B (Word.singletonValuation x) _ ↔
        EEquationSet.Satisfies B (Word.singletonValuation x) _
      rw [homogeneousTruncation_comp_domain sig hm hn,
        homogeneousTruncation_domain_of_lt sig (lt_trans hm hn)]
      constructor
      · intro hx t e he
        exact hx t e (Or.inr he)
      · intro hx t e he
        rcases he with he | he
        · have hmcell := (satisfies_truncationEquation_iff B hB ⟨m, lt_trans hm hn⟩ s x).mp hx
          have hncell := ((recoveredAlgebra B hB).sort s).str.isCell_mono
            (show (⟨m, lt_trans hm hn⟩ : Fin p) ≤ ⟨n, hn⟩ from hm.le) hmcell
          exact (satisfies_truncationEquation_iff B hB ⟨n, hn⟩ s x).mpr hncell t e he
        · exact hx t e he
    · have he : (homogeneousTruncation sig hmn).comp
          (homogeneousTruncation sig (le_refl n)) = homogeneousTruncation sig hmn := by
        rw [homogeneousTruncation_self, GeneralizedHepDerivor.comp_identity]
      have heD := congrFun (eq_of_heq (hepDomain_heq
        (c := (homogeneousTruncation sig hmn).comp (homogeneousTruncation sig (le_refl n)))
        (d := homogeneousTruncation sig hmn) he)) s
      change EEquationSet.Satisfies B (Word.singletonValuation x) _ ↔ _
      rw [heD]
      rfl
  · have he : (homogeneousTruncation sig (le_refl m)).comp
        (homogeneousTruncation sig hnp) = homogeneousTruncation sig hnp := by
      rw [homogeneousTruncation_self, GeneralizedHepDerivor.identity_comp]
    have heD := congrFun (eq_of_heq (hepDomain_heq
      (c := (homogeneousTruncation sig (le_refl m)).comp (homogeneousTruncation sig hnp))
      (d := homogeneousTruncation sig hnp) he)) s
    change EEquationSet.Satisfies B (Word.singletonValuation x) _ ↔ _
    rw [heD]
    rfl

/-- Every element satisfies the homogeneous mixed upper composite domain. -/
theorem homogeneousMixed_upper_isCell {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin m) sig))
    (s : S) (x : B.carrier s) :
    ((homogeneousTruncation sig hnp).comp
      (homogeneousDiscretization sig (le_trans hmn hnp))).IsCell B s x := by
  change EEquationSet.Satisfies B (Word.singletonValuation x) _
  rcases hnp.lt_or_eq with hn | rfl
  · rw [homogeneousMixed_upper_domain sig hmn hn]
    exact satisfies_reflexiveEquation B s x
  · change EEquationSet.Satisfies B (Word.singletonValuation x)
      (⊥ ⊔ (homogeneousDiscretizationDerivor sig n m).translateSingletonSet s
        ((homogeneousTruncation sig (le_refl n)).domain s))
    erw [homogeneousTruncation_domain_self, Derivor.translateSingletonSet_empty, bot_sup_eq]
    exact fun _ _ he => he.elim

/-- The comparison for successive homogeneous truncations is surjective in every model. -/
theorem homogeneousTruncation_comparison_surjective {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin p) sig))
    (hB : (Homogeneous.specification (Fin p) sig).IsModel B) :
    ∀ s, Function.Surjective
      (((homogeneousTruncation sig hmn).comparison (homogeneousTruncation sig hnp) B).toMap s) := by
  rcases hmn.lt_or_eq with hm | rfl
  · apply ((homogeneousTruncation sig hmn).comparison_surjective_iff (homogeneousTruncation sig hnp) B).mpr
    intro s x hx
    change EEquationSet.Satisfies B _
      ((homogeneousTruncationDerivor sig hnp).translateSingletonSet s
        ((homogeneousTruncation sig hmn).domain s)) at hx
    rw [homogeneousTruncation_domain_of_lt sig hm, truncation_translate_equation] at hx
    change EEquationSet.Satisfies _ _ ((homogeneousTruncation sig hmn).domain s)
    rw [homogeneousTruncation_domain_of_lt sig hm]
    apply (satisfies_truncationEquation_iff _
      (homogeneousTruncation_isModel sig hnp B hB) ⟨m, hm⟩ s x).mpr
    apply Subtype.ext
    exact (truncation_boundary_val hnp B hB ⟨m, hm⟩ false s x).trans
      ((satisfies_truncationEquation_iff B hB (dimensionInclusion hnp ⟨m, hm⟩) s x.val).mp hx)
  · exact (homogeneousTruncation sig (le_refl m)).comparison_surjective_of_empty
      (homogeneousTruncation sig hnp) B (homogeneousTruncation_domain_self sig m)

/-- A truncation after a discretization has surjective canonical comparison on models,
regardless of the relative positions of their cutoffs. -/
theorem homogeneousMixed_comparison_surjective {q r p : ℕ} (hqp : q ≤ p) (hrp : r ≤ p)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin r) sig))
    (hB : (Homogeneous.specification (Fin r) sig).IsModel B) :
    ∀ s, Function.Surjective
      (((homogeneousTruncation sig hqp).comparison (homogeneousDiscretization sig hrp) B).toMap s) := by
  rcases hqp.lt_or_eq with hq | rfl
  · apply ((homogeneousTruncation sig hqp).comparison_surjective_iff (homogeneousDiscretization sig hrp) B).mpr
    intro s x hx
    change EEquationSet.Satisfies _ _ ((homogeneousTruncation sig hqp).domain s)
    rw [homogeneousTruncation_domain_of_lt sig hq]
    apply (satisfies_truncationEquation_iff _
      (homogeneousDiscretization_isModel sig hrp B hB) ⟨q, hq⟩ s x).mpr
    apply Subtype.ext
    have hv := discretization_boundary_val hrp B hB ⟨q, hq⟩ false s x
    by_cases hqr : q < r
    · change EEquationSet.Satisfies B _
        ((homogeneousDiscretizationDerivor sig p r).translateSingletonSet s
          ((homogeneousTruncation sig hqp).domain s)) at hx
      rw [homogeneousTruncation_domain_of_lt sig hq,
        discretization_translate_equation_of_lt sig hrp _ hqr] at hx
      erw [dite_eq_left hqr] at hv
      exact hv.trans ((satisfies_truncationEquation_iff B hB ⟨q, hqr⟩ s x.val).mp hx)
    · erw [dite_eq_right hqr] at hv
      exact hv
  · exact (homogeneousTruncation sig (le_refl q)).comparison_surjective_of_empty
      (homogeneousDiscretization sig hrp) B (homogeneousTruncation_domain_self sig q)


/-- The mixed lower homogeneous composite selects exactly the cells of truncation. -/
theorem homogeneousMixed_lower_sameCells {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (s : S) (x : B.carrier s) :
    ((homogeneousTruncation sig (le_trans hmn hnp)).comp
      (homogeneousDiscretization sig hnp)).IsCell B s x ↔
        (homogeneousTruncation sig hmn).IsCell B s x := by
  rcases hmn.lt_or_eq with hm | rfl
  · have he := homogeneousMixed_lower sig hm hnp
    have heD := congrFun (eq_of_heq (hepDomain_heq
      (c := (homogeneousTruncation sig (le_trans hm.le hnp)).comp
        (homogeneousDiscretization sig hnp)) (d := homogeneousTruncation sig hm.le) he)) s
    change EEquationSet.Satisfies B (Word.singletonValuation x) _ ↔ _
    rw [heD]
    rfl
  · exact ⟨fun _ => (homogeneousTruncation sig (le_refl m)).isCell_of_empty
      (homogeneousTruncation_domain_self sig m) B s x,
      fun _ => homogeneousMixed_upper_isCell (le_refl m) hnp B s x⟩

end CategorialAlgebras.Dimensions
