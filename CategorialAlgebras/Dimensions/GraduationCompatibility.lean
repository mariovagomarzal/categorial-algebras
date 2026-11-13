import CategorialAlgebras.Dimensions.GraduationCells
import CategorialAlgebras.Dimensions.CompatibilityComparison
import CategorialAlgebras.Presentations.GraduationModels

/-!
# Graduation commutes with finite dimension changes

The two graduation squares are the canonical comparisons of induced functors,
restricted and corestricted to models and transported to categorial algebras.
Their components are identities on underlying elements.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} (sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n)

/-- Truncation commutes with graduation on models by comparison of derivors and cells. -/
noncomputable def truncationGraduationModels :
    graduationModels.{u, v, w} n sig ⋙ heterogeneousTruncationModels sig h ≅
      homogeneousTruncationModels sig h ⋙ graduationModels m sig :=
  inducedSquareModelsNatIso _ _ _ _ (truncation_graduation_derivor sig h) _ _ _ _
    (heterogeneousTruncation_isModel sig h) (graduation_isModel n sig)
    (graduation_isModel m sig) (homogeneousTruncation_isModel sig h)
    (fun B _ => (heterogeneousTruncation sig h).comparison_surjective_of_empty
      (graduation n sig) B (fun _ => rfl))
    (graduation_truncation_comparison_surjective h)
    (fun B hB p x => by
      change _ ↔ ((graduation m sig).comp (homogeneousTruncation sig h)).IsCell B p x
      exact truncation_graduation_sameCells h B hB p.1 p.2 x)

/-- The truncation-graduation comparison is identity on underlying elements. -/
theorem truncationGraduationModels_hom_val
    (B : (Homogeneous.specification (Fin n) sig).Models) (p)
    (x : ((graduationModels n sig ⋙ heterogeneousTruncationModels sig h).obj B).obj.obj.carrier p) :
    ((((truncationGraduationModels sig h).hom.app B).hom.hom.toMap p x).val).val = x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_hom_heq (heterogeneousTruncation sig h) (graduation n sig) (graduation m sig) (homogeneousTruncation sig h)
    _ _ _ _ _ _ _ _ _ _ _ _ B p x)

/-- The inverse truncation-graduation comparison is also identity on elements. -/
theorem truncationGraduationModels_inv_val
    (B : (Homogeneous.specification (Fin n) sig).Models) (p)
    (x : ((homogeneousTruncationModels sig h ⋙ graduationModels m sig).obj B).obj.obj.carrier p) :
    ((((truncationGraduationModels sig h).inv.app B).hom.hom.toMap p x).val).val = x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_inv_heq (heterogeneousTruncation sig h) (graduation n sig) (graduation m sig) (homogeneousTruncation sig h)
    _ _ _ _ _ _ _ _ _ _ _ _ B p x)

/-- Discretization commutes with graduation on models by comparison of derivors and cells. -/
noncomputable def discretizationGraduationModels :
    homogeneousDiscretizationModels.{u, v, w} sig h ⋙ graduationModels n sig ≅
      graduationModels m sig ⋙ heterogeneousDiscretizationModels sig h :=
  inducedSquareModelsNatIso _ _ _ _ (discretization_graduation_derivor sig h) _ _ _ _
    (graduation_isModel n sig) (homogeneousDiscretization_isModel sig h)
    (heterogeneousDiscretization_isModel sig h) (graduation_isModel m sig)
    (graduation_discretization_comparison_surjective h)
    (fun B _ => (heterogeneousDiscretization sig h).comparison_surjective_of_empty
      (graduation m sig) B (fun _ => rfl))
    (fun B _ p x => by
      change _ ↔ ((heterogeneousDiscretization sig h).comp (graduation m sig)).IsCell B p x
      exact discretization_graduation_sameCells h B p.1 p.2 x)

/-- The discretization-graduation comparison is identity on underlying elements. -/
theorem discretizationGraduationModels_hom_val
    (B : (Homogeneous.specification (Fin m) sig).Models) (p)
    (x : ((homogeneousDiscretizationModels sig h ⋙ graduationModels n sig).obj B).obj.obj.carrier p) :
    ((((discretizationGraduationModels sig h).hom.app B).hom.hom.toMap p x).val).val = x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_hom_heq (graduation n sig) (homogeneousDiscretization sig h) (heterogeneousDiscretization sig h) (graduation m sig)
    _ _ _ _ _ _ _ _ _ _ _ _ B p x)

/-- The inverse discretization-graduation comparison is also identity on elements. -/
theorem discretizationGraduationModels_inv_val
    (B : (Homogeneous.specification (Fin m) sig).Models) (p)
    (x : ((graduationModels m sig ⋙ heterogeneousDiscretizationModels sig h).obj B).obj.obj.carrier p) :
    ((((discretizationGraduationModels sig h).inv.app B).hom.hom.toMap p x).val).val = x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_inv_heq (graduation n sig) (homogeneousDiscretization sig h) (heterogeneousDiscretization sig h) (graduation m sig)
    _ _ _ _ _ _ _ _ _ _ _ _ B p x)

/-- Truncation commutes with graduation between categorial algebras.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def truncationGraduationFunctor :
    graduationFunctor.{u, v, w} n sig ⋙ heterogeneousTruncationFunctor sig h ≅
      homogeneousTruncationFunctor sig h ⋙ graduationFunctor m sig :=
  conjugateSquareIso Homogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism Heterogeneous.modelIsomorphism (truncationGraduationModels sig h)

/-- Discretization commutes with graduation between categorial algebras.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def discretizationGraduationFunctor :
    homogeneousDiscretizationFunctor.{u, v, w} sig h ⋙ graduationFunctor n sig ≅
      graduationFunctor m sig ⋙ heterogeneousDiscretizationFunctor sig h :=
  conjugateSquareIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism (discretizationGraduationModels sig h)

end CategorialAlgebras.Dimensions
