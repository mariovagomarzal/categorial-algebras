import CategorialAlgebras.Dimensions.OmegaComposition
import CategorialAlgebras.Limits.ProjectiveSystem

/-!
# Coherence of the truncation systems

Canonical truncation comparisons flatten nested cell subtypes without changing
the underlying element. This proves the associativity and unit coherences of
the projective systems and of the cones in natural dimensions.
-/

universe u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

variable {S : Type u} (sig : Signature.{u, v} S)

/-- Equality of model morphisms follows from equality on their sorted elements. -/
theorem model_hom_ext {R : Type*} {σ : EPSignature R} {E : EPSpecification σ}
    {A B : E.Models} {f g : A ⟶ B}
    (h : ∀ s x, f.hom.hom.toMap s x = g.hom.hom.toMap s x) : f = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply PartialAlgebra.Hom.ext
  funext s x
  exact h s x

/-- Finite homogeneous composition comparisons retain the underlying element. -/
theorem homogeneousComposition_val {m n p : ℕ} (h : m ≤ n) (k : n ≤ p)
    (A : (Homogeneous.specification (Fin p) sig).Models) (s) (x) :
    (((homogeneousTruncationModelsComp.{u, v, w} sig h k).hom.app A).hom.hom.toMap s x).val =
      x.val.val := by
  exact eq_of_heq (inducedCompositeModelsNatIso_hom_heq
    (homogeneousTruncation sig h) (homogeneousTruncation sig k)
    (homogeneousTruncation sig (le_trans h k)) (homogeneousTruncation_comp_derivor sig h k)
    (Homogeneous.specification (Fin m) sig) (Homogeneous.specification (Fin n) sig)
    (Homogeneous.specification (Fin p) sig)
    (homogeneousTruncation_isModel sig h) (homogeneousTruncation_isModel sig k)
    (homogeneousTruncation_isModel sig (le_trans h k))
    (homogeneousTruncation_comparison_surjective h k)
    (fun B hB s x => homogeneousTruncation_comp_sameCells h k B hB s x) A s x)

/-- Finite heterogeneous composition comparisons retain the underlying element. -/
theorem heterogeneousComposition_heq {m n p : ℕ} (h : m ≤ n) (k : n ≤ p)
    (A : (Heterogeneous.specification (Fin (p + 1)) sig).Models) (s) (x) :
    HEq ((((heterogeneousTruncationModelsComp.{u, v, w} sig h k).hom.app A).hom.hom.toMap s x).val)
      x.val.val := by
  exact inducedCompositeModelsNatIso_hom_heq
    (heterogeneousTruncation sig h) (heterogeneousTruncation sig k)
    (heterogeneousTruncation sig (le_trans h k))
    (congrArg GeneralizedHepDerivor.toDerivor (heterogeneousTruncation_comp sig h k))
    (Heterogeneous.specification (Fin (m + 1)) sig) (Heterogeneous.specification (Fin (n + 1)) sig)
    (Heterogeneous.specification (Fin (p + 1)) sig)
    (heterogeneousTruncation_isModel sig h) (heterogeneousTruncation_isModel sig k)
    (heterogeneousTruncation_isModel sig (le_trans h k))
    (fun B _ => (heterogeneousTruncation sig h).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ s x => cells_of_eq (heterogeneousTruncation_comp sig h k) B s x) A s x

/-- The homogeneous cone comparisons retain the underlying element. -/
theorem homogeneousCone_val {m n : ℕ} (h : m ≤ n)
    (A : Homogeneous.OmegaModels.{u, v, w} sig) (s) (x) :
    (((homogeneousOmegaTruncationModelsComp sig h).hom.app A).hom.hom.toMap s x).val =
      x.val.val := by
  exact eq_of_heq (inducedCompositeModelsNatIso_hom_heq
    (homogeneousTruncation sig h) (homogeneousOmegaTruncation sig n)
    (homogeneousOmegaTruncation sig m) (homogeneousOmegaTruncation_comp_derivor sig h)
    (Homogeneous.specification (Fin m) sig) (Homogeneous.specification (Fin n) sig)
    (Homogeneous.specification ℕ sig)
    (homogeneousTruncation_isModel sig h) (homogeneousOmegaTruncation_isModel sig n)
    (homogeneousOmegaTruncation_isModel sig m)
    (homogeneousOmegaTruncation_comparison_surjective sig h)
    (fun B hB s x => homogeneousOmegaTruncation_sameCells sig h B hB s x) A.obj s x)

/-- The heterogeneous cone comparisons retain the underlying element. -/
theorem heterogeneousCone_heq {m n : ℕ} (h : m ≤ n)
    (A : (Heterogeneous.specification ℕ sig).Models) (s) (x) :
    HEq ((((heterogeneousOmegaTruncationModelsComp.{u, v, w} sig h).hom.app A).hom.hom.toMap s x).val)
      x.val.val := by
  exact inducedCompositeModelsNatIso_hom_heq
    (heterogeneousTruncation sig h) (heterogeneousOmegaTruncation sig n)
    (heterogeneousOmegaTruncation sig m)
    (congrArg GeneralizedHepDerivor.toDerivor (heterogeneousOmegaTruncation_comp sig h))
    (Heterogeneous.specification (Fin (m + 1)) sig) (Heterogeneous.specification (Fin (n + 1)) sig)
    (Heterogeneous.specification ℕ sig)
    (heterogeneousTruncation_isModel sig h) (heterogeneousOmegaTruncation_isModel sig n)
    (heterogeneousOmegaTruncation_isModel sig m)
    (fun B _ => (heterogeneousTruncation sig h).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ s x => cells_of_eq (heterogeneousOmegaTruncation_comp sig h) B s x) A s x

/-- Equal-dimensional homogeneous truncation forgets only the cell proof. -/
theorem homogeneousIdentity_val (n : ℕ)
    (A : (Homogeneous.specification (Fin n) sig).Models) (s) (x) :
    ((homogeneousTruncationModelsSelf.{u, v, w} sig n).hom.app A).hom.hom.toMap s x = x.val := by
  exact eq_of_heq (inducedIdentityModelsIsoOfEq_hom_heq (homogeneousTruncation_self sig n)
    (Homogeneous.specification (Fin n) sig) (homogeneousTruncation_isModel sig (le_refl n)) A s x)

/-- Equal-dimensional heterogeneous truncation forgets only the cell proof. -/
theorem heterogeneousIdentity_heq (n : ℕ)
    (A : (Heterogeneous.specification (Fin (n + 1)) sig).Models) (s) (x) :
    HEq (((heterogeneousTruncationModelsSelf.{u, v, w} sig n).hom.app A).hom.hom.toMap s x) x.val := by
  exact inducedIdentityModelsIsoOfEq_hom_heq (heterogeneousTruncation_self sig n)
    (Heterogeneous.specification (Fin (n + 1)) sig) (heterogeneousTruncation_isModel sig (le_refl n)) A s x

/-- The projective system of homogeneous finite-dimensional models. -/
noncomputable def homogeneousSystem :
    ProjectiveSystem (fun n => (Homogeneous.specification (Fin n) sig).Models.{u, max v u, w, 0}) where
  truncation h := homogeneousTruncationModels sig h
  identity n := homogeneousTruncationModelsSelf sig n
  composition h k := homogeneousTruncationModelsComp sig h k
  associativity h k q A := by
    apply model_hom_ext
    intro s x
    apply Subtype.ext
    change (((homogeneousTruncationModelsComp sig h (le_trans k q)).hom.app A).hom.hom.toMap s
      (((homogeneousTruncationModels sig h).map ((homogeneousTruncationModelsComp sig k q).hom.app A)).hom.hom.toMap s x)).val =
      (((homogeneousTruncationModelsComp sig (le_trans h k) q).hom.app A).hom.hom.toMap s
        (((homogeneousTruncationModelsComp sig h k).hom.app _).hom.hom.toMap s x)).val
    rw [homogeneousComposition_val, homogeneousComposition_val, homogeneousComposition_val,
      homogeneousTruncationModels_map_val]
    exact homogeneousComposition_val sig k q A s x.val
  identity_lower h A := by
    apply model_hom_ext
    intro s x
    apply Subtype.ext
    rw [homogeneousComposition_val, homogeneousIdentity_val]
  identity_upper h A := by
    apply model_hom_ext
    intro s x
    apply Subtype.ext
    rw [homogeneousComposition_val, homogeneousTruncationModels_map_val]
    exact (homogeneousIdentity_val sig _ _ _ _).symm
/-- The projective system of heterogeneous finite-dimensional models. -/
noncomputable def heterogeneousSystem :
    ProjectiveSystem (fun n => (Heterogeneous.specification (Fin (n + 1)) sig).Models.{u, max v u, w, 0}) where
  truncation h := heterogeneousTruncationModels sig h
  identity n := heterogeneousTruncationModelsSelf sig n
  composition h k := heterogeneousTruncationModelsComp sig h k
  associativity h k q A := by
    apply model_hom_ext
    intro s x
    apply Subtype.ext
    change (((heterogeneousTruncationModelsComp sig h (le_trans k q)).hom.app A).hom.hom.toMap s
      (((heterogeneousTruncationModels sig h).map ((heterogeneousTruncationModelsComp sig k q).hom.app A)).hom.hom.toMap s x)).val =
      (((heterogeneousTruncationModelsComp sig (le_trans h k) q).hom.app A).hom.hom.toMap s
        (((heterogeneousTruncationModelsComp sig h k).hom.app _).hom.hom.toMap s x)).val
    apply eq_of_heq
    apply (heterogeneousComposition_heq sig h (le_trans k q) A s _).trans
    change HEq
      ((((heterogeneousTruncationModelsComp sig k q).hom.app A).hom.hom.toMap _ x.val).val)
      ((((heterogeneousTruncationModelsComp sig (le_trans h k) q).hom.app A).hom.hom.toMap s
        (((heterogeneousTruncationModelsComp sig h k).hom.app _).hom.hom.toMap s x)).val)
    exact (heterogeneousComposition_heq sig k q A _ x.val).trans
      ((heterogeneousComposition_heq sig (le_trans h k) q A s _).trans
        (heq_of_eq (congrArg Subtype.val (eq_of_heq
          (heterogeneousComposition_heq sig h k _ s x))))).symm
  identity_lower h A := by
    apply model_hom_ext
    intro s x
    apply Subtype.ext
    exact eq_of_heq ((heterogeneousComposition_heq sig (le_refl _) h A s x).trans
      (heq_of_eq (congrArg Subtype.val (eq_of_heq
        (heterogeneousIdentity_heq sig _ _ s x)))).symm)
  identity_upper h A := by
    apply model_hom_ext
    intro s x
    apply Subtype.ext
    exact eq_of_heq ((heterogeneousComposition_heq sig h (le_refl _) A s x).trans
      (heterogeneousIdentity_heq sig _ A _ x.val).symm)

/-- The homogeneous natural-dimensional models give a coherent cone of truncations. -/
noncomputable def homogeneousCone : Homogeneous.OmegaModels.{u, v, w} sig ⥤
    (homogeneousSystem.{u, v, w} sig).Family where
  obj A :=
    { obj n := (homogeneousOmegaTruncationModels sig n).obj A
      transition h := (homogeneousOmegaTruncationModelsComp sig h).app A
      identity n := by
        apply model_hom_ext
        intro s x
        apply Subtype.ext
        exact (homogeneousCone_val sig (le_refl n) A s x).trans
          (congrArg Subtype.val (homogeneousIdentity_val sig n _ s x)).symm
      coherence h k := by
        apply model_hom_ext
        intro s x
        apply Subtype.ext
        change (((homogeneousOmegaTruncationModelsComp sig h).hom.app A).hom.hom.toMap s
          (((homogeneousTruncationModels sig h).map
            ((homogeneousOmegaTruncationModelsComp sig k).hom.app A)).hom.hom.toMap s x)).val =
          (((homogeneousOmegaTruncationModelsComp sig (le_trans h k)).hom.app A).hom.hom.toMap s
            (((homogeneousTruncationModelsComp sig h k).hom.app _).hom.hom.toMap s x)).val
        rw [homogeneousCone_val, homogeneousCone_val]
        change (((homogeneousOmegaTruncationModelsComp sig k).hom.app A).hom.hom.toMap s x.val).val = _
        exact (homogeneousCone_val sig k A s x.val).trans
          (congrArg Subtype.val (homogeneousComposition_val sig h k _ s x)).symm }
  map f :=
    { app n := (homogeneousOmegaTruncationModels sig n).map f
      comm h := (homogeneousOmegaTruncationModelsComp sig h).hom.naturality f }
  map_id A := by
    apply ProjectiveSystem.Family.Hom.ext
    funext n
    exact (homogeneousOmegaTruncationModels sig n).map_id A
  map_comp f g := by
    apply ProjectiveSystem.Family.Hom.ext
    funext n
    exact (homogeneousOmegaTruncationModels sig n).map_comp f g

/-- The heterogeneous natural-dimensional models give a coherent cone of truncations. -/
noncomputable def heterogeneousCone : (Heterogeneous.specification ℕ sig).Models.{u, max v u, w, 0} ⥤
    (heterogeneousSystem.{u, v, w} sig).Family where
  obj A :=
    { obj n := (heterogeneousOmegaTruncationModels sig n).obj A
      transition h := (heterogeneousOmegaTruncationModelsComp sig h).app A
      identity n := by
        apply model_hom_ext
        intro s x
        apply Subtype.ext
        exact eq_of_heq ((heterogeneousCone_heq sig (le_refl n) A s x).trans
          (heq_of_eq (congrArg Subtype.val (eq_of_heq
          (heterogeneousIdentity_heq sig n _ s x)))).symm)
      coherence h k := by
        apply model_hom_ext
        intro s x
        apply Subtype.ext
        change (((heterogeneousOmegaTruncationModelsComp sig h).hom.app A).hom.hom.toMap s
          (((heterogeneousTruncationModels sig h).map
            ((heterogeneousOmegaTruncationModelsComp sig k).hom.app A)).hom.hom.toMap s x)).val =
          (((heterogeneousOmegaTruncationModelsComp sig (le_trans h k)).hom.app A).hom.hom.toMap s
            (((heterogeneousTruncationModelsComp sig h k).hom.app _).hom.hom.toMap s x)).val
        apply eq_of_heq
        apply (heterogeneousCone_heq sig h A s _).trans
        exact (heterogeneousCone_heq sig k A _ x.val).trans
          ((heterogeneousCone_heq sig (le_trans h k) A s _).trans
            (heq_of_eq (congrArg Subtype.val (eq_of_heq
          (heterogeneousComposition_heq sig h k _ s x))))).symm }
  map f :=
    { app n := (heterogeneousOmegaTruncationModels sig n).map f
      comm h := (heterogeneousOmegaTruncationModelsComp sig h).hom.naturality f }
  map_id A := by
    apply ProjectiveSystem.Family.Hom.ext
    funext n
    exact (heterogeneousOmegaTruncationModels sig n).map_id A
  map_comp f g := by
    apply ProjectiveSystem.Family.Hom.ext
    funext n
    exact (heterogeneousOmegaTruncationModels sig n).map_comp f g

end CategorialAlgebras.Limits
