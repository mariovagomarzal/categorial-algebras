import CategorialAlgebras.Limits.HeterogeneousGluing

/-!
# Finite restrictions of the heterogeneous diagonal

The charts identify each finite restriction of the diagonal algebra with the
given finite stage. These identifications form an isomorphism of compatible
families and retain exactly the prescribed diagonal transports.
-/

universe u v w
namespace CategorialAlgebras.Limits
open CategoryTheory Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (heterogeneousSystem.{u, v, w} sig).Family)

/-- The finite chart is a homomorphism from the restricted diagonal algebra to its stage. -/
noncomputable def heterogeneousChartHom (n : ℕ) :
    Heterogeneous.CategorialAlgebra.Hom
      (reindexedAlgebra (heterogeneousDiagonalAlgebra A) (omegaInclusion (n + 1)).toOrderHom
        (orderEmbedding_saturating _)) (heterogeneousStage A n) where
  sort s :=
    { toFun j := heterogeneousStageUp A (Nat.le_of_lt_succ j.isLt) s
      map_source j k h x := by
        change heterogeneousStageUp A _ s ((dimensionLE (heterogeneousDiagonalSort A s).str
          (show j.val ≤ k.val from h.le)).source x) = _
        rw [dimensionLE_of_lt _ _ (show j.val < k.val from h)]
        exact heterogeneousChart_source A (show j.val < k.val from h) _ s x
      map_target j k h x := by
        change heterogeneousStageUp A _ s ((dimensionLE (heterogeneousDiagonalSort A s).str
          (show j.val ≤ k.val from h.le)).target x) = _
        rw [dimensionLE_of_lt _ _ (show j.val < k.val from h)]
        exact heterogeneousChart_target A (show j.val < k.val from h) _ s x
      map_identity j k h x := by
        change heterogeneousStageUp A _ s ((dimensionLE (heterogeneousDiagonalSort A s).str
          (show j.val ≤ k.val from h.le)).identity x) = _
        rw [dimensionLE_of_lt _ _ (show j.val < k.val from h)]
        exact heterogeneousChart_identity A (show j.val < k.val from h) _ s x
      map_comp j k h x y z hz := by
        change z ∈ (dimensionLE (heterogeneousDiagonalSort A s).str
          (show j.val ≤ k.val from h.le)).comp x y at hz
        rw [dimensionLE_of_lt _ _ (show j.val < k.val from h)] at hz
        exact (heterogeneousChart_comp A (show j.val < k.val from h) _ s x y z).mpr hz }
  map_op σ j x := heterogeneousChart_op A σ (k := j.val) (n := n)
    (Nat.le_of_lt_succ j.isLt) x

/-- The finite chart is an isomorphism of partial algebras. -/
noncomputable def heterogeneousChartIso (n : ℕ) :
    (reindexedAlgebra (heterogeneousDiagonalAlgebra A) (omegaInclusion (n + 1)).toOrderHom
      (orderEmbedding_saturating _)).toPartialAlgebra ≅ (heterogeneousStage A n).toPartialAlgebra := by
  let f :
      (reindexedAlgebra (heterogeneousDiagonalAlgebra A) (omegaInclusion (n + 1)).toOrderHom
        (orderEmbedding_saturating _)).toPartialAlgebra ⟶ (heterogeneousStage A n).toPartialAlgebra :=
    (heterogeneousChartHom A n).toPartialHom
  have : IsIso f := (Heterogeneous.hepSignature (Fin (n + 1)) sig).isIso_of_bijective
    (Heterogeneous.equations_isEPAlgebra (reindexedAlgebra (heterogeneousDiagonalAlgebra A)
      (omegaInclusion (n + 1)).toOrderHom (orderEmbedding_saturating _)).satisfiesEquations)
    (EPSignature.IsEPAlgebra.isWeak
      (Heterogeneous.equations_isEPAlgebra (heterogeneousStage A n).satisfiesEquations)) f
    (fun p => heterogeneousStageMap_bijective A (Nat.le_of_lt_succ p.1.isLt) (Fin.last p.1.val) p.2)
  exact asIso f

/-- The explicit diagonal partial algebra, bundled as a model. -/
noncomputable def heterogeneousDiagonalModel : (Heterogeneous.specification ℕ sig).Models :=
  ⟨⟨heterogeneousDiagonalPartial A, (heterogeneousDiagonal_isModel A).1⟩,
    (heterogeneousDiagonal_isModel A).2⟩

/-- The partial-algebra comparison from a finite restriction to its original stage. -/
noncomputable def heterogeneousDiagonalFiniteIso (n : ℕ) :
    ((heterogeneousOmegaTruncation sig n).transformed (heterogeneousDiagonalPartial A)) ≅
      (A.obj n).obj.obj :=
  ((heterogeneousOmegaTruncation sig n).transformedFunctor.mapIso
    (eqToIso (heterogeneousDiagonalAlgebra_expansion A))).symm ≪≫
    (heterogeneousDimensionRealization sig (omegaInclusion (n + 1)).toOrderHom
      (orderEmbedding_saturating _) (heterogeneousDiagonalAlgebra A)).symm ≪≫
    heterogeneousChartIso A n ≪≫ heterogeneousStageIso A n

/-- The finite diagonal comparison transports an element upwards to its finite stage. -/
theorem heterogeneousDiagonalFiniteIso_hom (n : ℕ) (j : Fin (n + 1)) (s : S) (x) :
    (heterogeneousDiagonalFiniteIso A n).hom.toMap (j, s) x =
      heterogeneousStageUp A (Nat.le_of_lt_succ j.isLt) s x.val := by
  change (heterogeneousStageIso A n).hom.toMap (j, s)
    ((heterogeneousChartIso A n).hom.toMap (j, s)
      ((heterogeneousDimensionRealization sig (omegaInclusion (n + 1)).toOrderHom _ _).inv.toMap (j, s)
        (((heterogeneousOmegaTruncation sig n).transformedFunctor.mapIso
          (eqToIso (heterogeneousDiagonalAlgebra_expansion A))).inv.toMap (j, s) x))) = _
  erw [heterogeneousStageIso_hom, dimensionRealization_inv]
  change heterogeneousStageUp A _ s ((eqToHom (heterogeneousDiagonalAlgebra_expansion A).symm).toMap _ x.val) = _
  erw [fixedCarrier_eqToHom]

/-- Inverse finite diagonal comparisons transport cells downwards to their own dimension. -/
theorem heterogeneousDiagonalFiniteIso_inv (n : ℕ) (j : Fin (n + 1)) (s : S) (x) :
    ((heterogeneousDiagonalFiniteIso A n).inv.toMap (j, s) x).val =
      heterogeneousStageDown A (Nat.le_of_lt_succ j.isLt) s x := by
  apply heterogeneousChart_injective A (Nat.le_of_lt_succ j.isLt) s
  rw [heterogeneousStageUp_down]
  have he := congrArg (fun g => g.toMap (j, s) x) (heterogeneousDiagonalFiniteIso A n).inv_hom_id
  exact (heterogeneousDiagonalFiniteIso_hom A n j s _).symm.trans he

/-- A finite stage transport cancels the forward transition isomorphism. -/
theorem heterogeneousStageMap_transition {m n : ℕ} (h : m ≤ n) (j : Fin (m + 1)) (s) (x) :
    heterogeneousStageMap A h j s ((A.transition h).hom.hom.hom.toMap (j, s) x) = x.val :=
  congrArg (fun g => (g.hom.hom.toMap (j, s) x).val) (A.transition h).hom_inv_id

/-- The diagonal finite comparisons form an isomorphism of compatible families. -/
noncomputable def heterogeneousDiagonalComparison :
    (heterogeneousCone sig).obj (heterogeneousDiagonalModel A) ≅ A :=
  ProjectiveSystem.Family.isoMk _
    (fun n => modelIso _ _ (heterogeneousDiagonalFiniteIso A n)) (by
      intro m n h
      apply model_hom_ext
      intro p x
      apply (heterogeneousStageMap_bijective A h p.1 p.2).1
      change heterogeneousStageMap A h p.1 p.2
        ((A.transition h).hom.hom.hom.toMap p
          (((heterogeneousTruncationModels sig h).map
            (modelIso _ _ (heterogeneousDiagonalFiniteIso A n)).hom).hom.hom.toMap p x)) =
        heterogeneousStageMap A h p.1 p.2
          ((heterogeneousDiagonalFiniteIso A m).hom.toMap p
            (((heterogeneousOmegaTruncationModelsComp sig h).hom.app
              (heterogeneousDiagonalModel A)).hom.hom.toMap p x))
      rw [heterogeneousStageMap_transition]
      change (heterogeneousDiagonalFiniteIso A n).hom.toMap (cellInclusion h p.1, p.2) x.val = _
      erw [heterogeneousDiagonalFiniteIso_hom, heterogeneousDiagonalFiniteIso_hom,
        heterogeneousStageUp_trans]
      have hv := eq_of_heq (heterogeneousCone_heq sig h (heterogeneousDiagonalModel A) p x)
      exact congrArg (heterogeneousStageUp A _ p.2) hv.symm)

end CategorialAlgebras.Limits
