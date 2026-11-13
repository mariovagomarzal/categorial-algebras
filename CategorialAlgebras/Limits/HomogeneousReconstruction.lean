import CategorialAlgebras.Limits.HomogeneousGluing

/-!
# Finite restrictions of the homogeneous union

The $n$-cells of the union are exactly the image of stage $n$. Original
operations and lower-dimensional structures have their original values on
these cells. The resulting isomorphisms form a coherent family comparison.
-/

universe u v w
namespace CategorialAlgebras.Limits
open CategoryTheory Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (homogeneousSystem.{u, v, w} sig).Family)

/-- The truncation domain in the union is precisely the fixed-source condition. -/
theorem homogeneousUnionCell_iff (n : ℕ) (s) (x : HomogeneousUnion A s) :
    (homogeneousOmegaTruncation sig n).IsCell (homogeneousUnionPartial A) s x ↔
      homogeneousUnionSource A n s x = x := by
  constructor
  · intro hx
    obtain ⟨q, hq, hr⟩ := hx s (omegaTruncationEquation sig n s) ⟨rfl, rfl⟩
    have he : q = x := Part.mem_some_iff.mp hq
    change q ∈ Term.partialEval _ (Homogeneous.unary _ _) at hr
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some] at hr
    exact (Part.mem_some_iff.mp hr).symm.trans he
  · intro hx t e ⟨ht, he⟩
    cases ht
    cases he
    refine ⟨x, Part.mem_some _, ?_⟩
    change x ∈ Term.partialEval (A := homogeneousUnionPartial A) (Word.singletonValuation x)
      (Homogeneous.unary (.source n s) (.var (Word.position _ 0)))
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some_iff.mpr hx.symm

/-- Insert a finite-stage cell into the selected cutoff-cell carrier of the union. -/
def homogeneousUnionCell (n : ℕ) (s) (x : (A.obj n).obj.obj.carrier s) :
    (homogeneousOmegaTruncation sig n).Cell (homogeneousUnionPartial A) s :=
  ⟨homogeneousUnionIn A n s x, (homogeneousUnionCell_iff A n s _).mpr
    (homogeneousUnionIn_isCell A n s x)⟩

/-- Each cutoff-cell carrier of the union is exactly its original finite stage. -/
theorem homogeneousUnionCell_bijective (n : ℕ) (s) :
    Function.Bijective (homogeneousUnionCell A n s) := by
  constructor
  · intro x y h
    exact homogeneousUnionIn_injective A n s (congrArg Subtype.val h)
  · intro x
    have hc := (homogeneousUnionCell_iff A n s x.val).mp x.property
    obtain ⟨m, y, hy⟩ := homogeneousUnionIn_surjective A s x.val
    let p := max m (n+1)
    have hm : m ≤ p := le_max_left _ _
    have hn : n < p := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
    let y' := homogeneousStageInclusion A hm s y
    have hy' : homogeneousUnionIn A p s y' = x.val := (homogeneousUnionIn_inclusion A hm s y).symm.trans hy
    have hfix : (((homogeneousStage A p).sort s).str.dim ⟨n, hn⟩).source y' = y' := by
      apply homogeneousUnionIn_injective A p s
      calc
        _ = homogeneousUnionSource A n s (homogeneousUnionIn A p s y') :=
          (homogeneousUnionSource_in A ⟨n, hn⟩ s y').symm
        _ = _ := (congrArg (homogeneousUnionSource A n s) hy').trans (hc.trans hy'.symm)
    let z : ((homogeneousTruncationModels sig hn.le).obj (A.obj p)).obj.obj.carrier s :=
      ⟨y', (homogeneousTruncation_isCell_iff_model hn.le (A.obj p).obj.obj
        ⟨(A.obj p).obj.property, (A.obj p).property⟩ s y').mpr (fun _ => hfix)⟩
    let w := (A.transition hn.le).hom.hom.hom.toMap s z
    have hw : homogeneousStageInclusion A hn.le s w = y' :=
      congrArg (fun g => (g.hom.hom.toMap s z).val) (A.transition hn.le).hom_inv_id
    refine ⟨w, Subtype.ext ?_⟩
    exact (homogeneousUnionIn_inclusion A hn.le s w).trans
      ((congrArg (homogeneousUnionIn A p s) hw).trans hy')

/-- The union operations have the required interpreting values on each finite stage. -/
theorem homogeneousUnion_imageValue (n : ℕ)
    {a s} (σ : Homogeneous.Symbol (Fin n) sig a s)
    (x : Word.Family (homogeneousStage A n).carrier a) {q}
    (hq : q ∈ (homogeneousStage A n).toPartialAlgebra.op σ x) :
    (homogeneousUnionCell A n s q).val ∈
      (homogeneousOmegaTruncation sig n).imageValue (homogeneousUnionPartial A) σ
        (fun j => homogeneousUnionCell A n _ (x j)) := by
  cases σ with
  | base σ =>
    apply (Term.mem_partialEval_app _ _ _ _).mpr
    refine ⟨(fun j => homogeneousUnionIn A n _ (x j)), (fun _ => Part.mem_some _), ?_⟩
    change homogeneousUnionIn A n s q ∈ Part.some _
    rw [homogeneousUnionBase_in]
    exact Part.mem_some_iff.mpr (congrArg (homogeneousUnionIn A n s) (Part.mem_some_iff.mp hq))
  | source k s =>
    change homogeneousUnionIn A n s q ∈ Term.partialEval (A := homogeneousUnionPartial A)
      (Word.valuation (φ := id) (fun j => homogeneousUnionIn A n _ (x j)))
      (Homogeneous.unary (.source k.val s) (.var (Word.position _ 0)))
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    change homogeneousUnionIn A n s q ∈ Part.some _
    erw [homogeneousUnionSource_in A k s]
    exact Part.mem_some_iff.mpr (congrArg (homogeneousUnionIn A n s) (Part.mem_some_iff.mp hq))
  | target k s =>
    change homogeneousUnionIn A n s q ∈ Term.partialEval (A := homogeneousUnionPartial A)
      (Word.valuation (φ := id) (fun j => homogeneousUnionIn A n _ (x j)))
      (Homogeneous.unary (.target k.val s) (.var (Word.position _ 0)))
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    change homogeneousUnionIn A n s q ∈ Part.some _
    erw [homogeneousUnionTarget_in A k s]
    exact Part.mem_some_iff.mpr (congrArg (homogeneousUnionIn A n s) (Part.mem_some_iff.mp hq))
  | comp k s =>
    change homogeneousUnionIn A n s q ∈ Term.partialEval (A := homogeneousUnionPartial A)
      (Word.valuation (φ := id) (fun j => homogeneousUnionIn A n _ (x j)))
      (Homogeneous.binary k.val (.var (Word.position _ 0)) (.var (Word.position _ 1)))
    erw [Homogeneous.partialEval_binary, Term.partialEval_var, Part.bind_some,
      Term.partialEval_var, Part.bind_some]
    exact (homogeneousUnionComp_mem A k s _ _ _).mpr hq

/-- Each finite stage realizes the corresponding truncation of the union. -/
noncomputable def homogeneousUnionRealization (n : ℕ) :
    (homogeneousStage A n).toPartialAlgebra ≅
      (homogeneousOmegaTruncation sig n).transformed (homogeneousUnionPartial A) :=
  realizationIso (homogeneousOmegaTruncation sig n) (homogeneousUnionPartial A)
    (homogeneousStage A n).toPartialAlgebra
    (Homogeneous.equations_isEPAlgebra (homogeneousStage A n).satisfiesEquations)
    (homogeneousUnionCell A n) (homogeneousUnionCell_bijective A n) (homogeneousUnion_imageValue A n)

/-- The finite comparison from the original stage into the union truncation. -/
noncomputable def homogeneousUnionFiniteIso (n : ℕ) :
    (A.obj n).obj.obj ≅ (homogeneousOmegaTruncation sig n).transformed (homogeneousUnionPartial A) :=
  (homogeneousStageIso A n).symm ≪≫ homogeneousUnionRealization A n

/-- The finite comparison inserts the original element into the union. -/
theorem homogeneousUnionFiniteIso_hom (n : ℕ) (s) (x) :
    ((homogeneousUnionFiniteIso A n).hom.toMap s x).val = homogeneousUnionIn A n s x := by
  change homogeneousUnionIn A n s ((homogeneousStageIso A n).inv.toMap s x) = _
  rw [homogeneousStageIso_inv]

/-- The explicit increasing union bundled as a finite-dimensional model. -/
noncomputable def homogeneousUnionModel : Homogeneous.OmegaModels.{u, v, w} sig :=
  ⟨⟨⟨homogeneousUnionPartial A, (homogeneousUnion_isModel A).1⟩,
    (homogeneousUnion_isModel A).2⟩, homogeneousUnion_finite A⟩

/-- A finite homogeneous stage inclusion cancels the forward transition on cutoff cells. -/
theorem homogeneousStageInclusion_transition {m n : ℕ} (h : m ≤ n) (s) (x) :
    homogeneousStageInclusion A h s ((A.transition h).hom.hom.hom.toMap s x) = x.val :=
  congrArg (fun g => (g.hom.hom.toMap s x).val) (A.transition h).hom_inv_id

/-- The finite comparisons give an isomorphism of compatible families. -/
noncomputable def homogeneousUnionComparison :
    (homogeneousCone sig).obj (homogeneousUnionModel A) ≅ A :=
  (ProjectiveSystem.Family.isoMk _
    (fun n => modelIso _ _ (homogeneousUnionFiniteIso A n)) (by
      intro m n h
      apply model_hom_ext
      intro s x
      apply Subtype.ext
      change (((homogeneousOmegaTruncationModelsComp sig h).hom.app (homogeneousUnionModel A)).hom.hom.toMap s
        (((homogeneousTruncationModels sig h).map (modelIso _ _ (homogeneousUnionFiniteIso A n)).hom).hom.hom.toMap s x)).val =
        ((homogeneousUnionFiniteIso A m).hom.toMap s ((A.transition h).hom.hom.hom.toMap s x)).val
      rw [homogeneousCone_val]
      change ((homogeneousUnionFiniteIso A n).hom.toMap s x.val).val = _
      rw [homogeneousUnionFiniteIso_hom, homogeneousUnionFiniteIso_hom]
      exact ((homogeneousUnionIn_inclusion A h s _).trans
        (congrArg (homogeneousUnionIn A n s) (homogeneousStageInclusion_transition A h s x))).symm)).symm

end CategorialAlgebras.Limits
