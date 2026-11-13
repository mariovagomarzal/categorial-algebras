import CategorialAlgebras.Presentations.IdentityImage

/-!
# Cells of the heterogeneous composite derivor

The composite selects exactly the top identities in each dimension. Its comparison
with the two successive transformations is invertible on models.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- At a lower sort the composite selects the fixed points of identity after source. -/
theorem composite_isCell_castSucc
    (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (k : Fin n) (s)
    (x : (A.sort s).carrier (Fin.last n)) :
    ((graduation n sig).comp (unification n sig)).IsCell A.toPartialAlgebra (k.castSucc, s) x ↔
      ((A.sort s).str.dim _ _ (castSucc_lt_last k)).identity
        (((A.sort s).str.dim _ _ (castSucc_lt_last k)).source x) = x := by
  change EEquationSet.Satisfies _ _ (⊥ ⊔
    (unificationDerivor n sig).translateSingletonSet s
      (if h : k.val < n then _ else _)) ↔ _
  erw [bot_sup_eq, dite_eq_left k.isLt]
  refine (satisfies_translated_singleton (unificationDerivor n sig)
    (graduationEquation n sig k s) A.toPartialAlgebra x).trans ?_
  have he : (unificationDerivor n sig).translateSingleton s (graduationEquation n sig k s).2 =
      Heterogeneous.identityTerm (castSucc_lt_last k)
        (Heterogeneous.boundary (castSucc_lt_last k) false (.var (Word.position _ 0))) := by
    change Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
      (X := Word.Variables [(Fin.last n, s)]) (.identity (castSucc_lt_last k) s) _ = _
    apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
      (.identity (castSucc_lt_last k) s))
    funext j
    fin_cases j
    apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
      (.source (castSucc_lt_last k) s))
    funext j
    fin_cases j
    rfl
  change (∃ q, q ∈ Part.some x ∧ q ∈ Term.partialEval (A := A.toPartialAlgebra)
    (Word.singletonValuation x)
    ((unificationDerivor n sig).translateSingleton s (graduationEquation n sig k s).2)) ↔ _
  erw [he, Heterogeneous.eval_expansion_identity, Heterogeneous.eval_expansion_boundary,
    Term.partialEval_var, Part.bind_some, Part.bind_some]
  constructor
  · rintro ⟨q, hq, hr⟩
    exact (Part.mem_some_iff.mp hr).symm.trans (Part.mem_some_iff.mp hq)
  · intro hx
    exact ⟨x, Part.mem_some _, Part.mem_some_iff.mpr hx.symm⟩

/-- At the top sort the heterogeneous composite has no restrictions. -/
theorem composite_isCell_last
    (A : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig)) (s)
    (x : A.carrier (Fin.last n, s)) :
    ((graduation n sig).comp (unification n sig)).IsCell A (Fin.last n, s) x := by
  intro t e he
  change e ∈ ((⊥ : EEquationSet _ _) ⊔
    (unificationDerivor n sig).translateSingletonSet s
      ((graduation n sig).domain (Fin.last n, s))) t at he
  erw [graduation_domain_last, Derivor.translateSingletonSet_empty, bot_sup_eq] at he
  exact he.elim

/-- The selected cells of the composite are exactly the images of top identities. -/
theorem composite_isCell_iff_identity_range
    (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (k s)
    (x : (A.sort s).carrier (Fin.last n)) :
    ((graduation n sig).comp (unification n sig)).IsCell A.toPartialAlgebra (k, s) x ↔
      x ∈ Set.range (topIdentity (A.sort s) k) := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · exact ⟨fun _ => ⟨x, by simp only [topIdentity_last, id_eq]⟩,
      fun _ => composite_isCell_last n sig A.toPartialAlgebra s x⟩
  · exact (composite_isCell_castSucc n sig A j s x).trans
      ((isFiniteCell_castSucc ((unifiedAlgebra A).sort s).str j x).symm.trans
        (finiteCell_iff_identity_range A _ s x))

/-- The comparison for the heterogeneous round trip is surjective on expansions. -/
theorem heterogeneous_comparison_surjective
    (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    ∀ p, Function.Surjective
      (((graduation n sig).comparison (unification n sig) A.toPartialAlgebra).toMap p) := by
  intro p x
  rcases p with ⟨k, s⟩
  have hx := (composite_isCell_iff_identity_range n sig A k s x.val).mp x.property
  obtain ⟨y, hy⟩ := hx
  let z := identityImageCell A k s y
  let e := (graduation n sig).transformedFunctor.mapIso (unificationRealization n sig A)
  let q := e.hom.toMap (k, s)
    ((eqToHom (graduation_transformed n sig (unifiedAlgebra A)).symm).toMap (k, s) z)
  refine ⟨q, Subtype.ext ?_⟩
  change ((eqToHom (graduation_transformed n sig (unifiedAlgebra A)).symm).toMap
    (k, s) z).val = x.val
  erw [partial_eqToHom_toMap]
  exact hy

/-- On heterogeneous models the canonical comparison is an isomorphism. -/
noncomputable def heterogeneousComparisonIso
    (A : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hA : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel A) :
    (graduation n sig).transformed ((unification n sig).transformed A) ≅
      ((graduation n sig).comp (unification n sig)).transformed A := by
  apply (graduation n sig).comparisonIso (unification n sig) A ?_
    (graduation_isModel n sig _ (unification_isModel n sig A hA)).1
  let C := Heterogeneous.ofEquations A (fun e => hA.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = A := Heterogeneous.toPartialAlgebra_ofEquations A _
  rw [← hc]
  exact heterogeneous_comparison_surjective n sig C

end CategorialAlgebras.Presentations
