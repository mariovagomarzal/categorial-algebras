import CategorialAlgebras.Omega.FiniteGraduation
import CategorialAlgebras.Limits.Assembly
import CategorialAlgebras.Dimensions.GraduationCompatibility

/-!
# The compatible family of finite graduations

Finite graduation after truncation gives a coherent family. The transition
isomorphisms combine the finite graduation square with composition of truncations.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} (sig : Signature.{u, v} S)

/-- The finite graduation of the $n$-cell algebra, in its exact model presentation. -/
noncomputable def finiteGraduationModels (n : ℕ) :
    Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤
      (Heterogeneous.specification (Fin (n+1)) sig).Models :=
  Homogeneous.omegaModelFunctor ⋙ homogeneousOmegaTruncationModels sig n ⋙
    Presentations.graduationModels n sig

/-- The canonical transition of finite graduation after infinite truncation. -/
noncomputable def graduationTransition {m n : ℕ} (h : m ≤ n) :
    finiteGraduationModels.{u, v, w} sig n ⋙ heterogeneousTruncationModels sig h ≅
      finiteGraduationModels sig m :=
  Functor.isoWhiskerLeft (Homogeneous.omegaModelFunctor ⋙ homogeneousOmegaTruncationModels sig n)
    (truncationGraduationModels sig h) ≪≫
    Functor.isoWhiskerLeft Homogeneous.omegaModelFunctor
      (Functor.isoWhiskerRight (homogeneousOmegaTruncationModelsComp sig h)
        (Presentations.graduationModels m sig))

/-- Every finite-family transition retains the original scalar element. -/
theorem graduationTransition_val {m n : ℕ} (h : m ≤ n)
    (A : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) (p) (x) :
    ((((graduationTransition sig h).hom.app A).hom.hom.toMap p x).val).val = x.val.val.val := by
  let y := ((truncationGraduationModels sig h).hom.app
    ((homogeneousOmegaTruncationModels sig n).obj (Homogeneous.omegaModelFunctor.obj A))).hom.hom.toMap p x
  have hy := truncationGraduationModels_hom_val sig h
    ((homogeneousOmegaTruncationModels sig n).obj (Homogeneous.omegaModelFunctor.obj A)) p x
  have hv := homogeneousCone_val sig h (Homogeneous.omegaModelFunctor.obj A) p.2 y.val
  exact hv.trans (congrArg Subtype.val hy)

/-- The family of finite graduations satisfies all projective coherences.

**Formally weaker** than the informal statement. Informally, these functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equalities become natural
isomorphisms that are the identity on elements. -/
noncomputable def graduationFamily :
    (heterogeneousSystem.{u, v, w} sig).FunctorFamily
      (Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) where
  functor := finiteGraduationModels sig
  transition := graduationTransition sig
  identity n A := by
    apply model_hom_ext
    intro p x
    apply Subtype.ext
    apply Subtype.ext
    exact (graduationTransition_val sig (le_refl n) A p x).trans
      (congrArg (fun z => z.val.val) (eq_of_heq (heterogeneousIdentity_heq sig n
        ((finiteGraduationModels sig n).obj A) p x))).symm
  coherence h k A := by
    apply model_hom_ext
    intro p x
    apply Subtype.ext
    apply Subtype.ext
    change (((graduationTransition sig h).hom.app A).hom.hom.toMap p
      (((heterogeneousTruncationModels sig h).map ((graduationTransition sig k).hom.app A)).hom.hom.toMap p x)).val.val =
      (((graduationTransition sig (le_trans h k)).hom.app A).hom.hom.toMap p
        (((heterogeneousTruncationModelsComp sig h k).hom.app
          ((finiteGraduationModels sig _).obj A)).hom.hom.toMap p x)).val.val
    rw [graduationTransition_val, graduationTransition_val]
    have he := heterogeneousComposition_heq sig h k ((finiteGraduationModels sig _).obj A) p x
    exact (graduationTransition_val sig k A _ x.val).trans
      (congrArg (fun z => z.val.val) (eq_of_heq he)).symm

end CategorialAlgebras.Omega
