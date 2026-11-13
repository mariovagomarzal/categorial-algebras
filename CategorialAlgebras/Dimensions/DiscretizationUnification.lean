import CategorialAlgebras.Dimensions.UnificationDerivors
import CategorialAlgebras.Dimensions.CompatibilityComparison
import CategorialAlgebras.Presentations.UnificationModels

/-!
# Discretization commutes with unification

Equality of the complete generalized hep-derivors gives a canonical square
comparison. Both directions retain the underlying top-dimensional cells,
including the equality transport from the clamped top dimension.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} (sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n)

/-- Discretization commutes with unification on model categories. -/
noncomputable def discretizationUnificationModels :
    heterogeneousDiscretizationModels.{u, v, w} sig h ⋙ unificationModels n sig ≅
      unificationModels m sig ⋙ homogeneousDiscretizationModels sig h :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor (discretization_unification sig h)) _ _ _ _
    (unification_isModel n sig) (heterogeneousDiscretization_isModel sig h)
    (homogeneousDiscretization_isModel sig h) (unification_isModel m sig)
    (fun B _ => (unification n sig).comparison_surjective_of_empty
      (heterogeneousDiscretization sig h) B (fun _ => rfl))
    (fun B _ => (homogeneousDiscretization sig h).comparison_surjective_of_empty
      (unification m sig) B (fun _ => rfl))
    (fun B _ => cells_of_eq (discretization_unification sig h) B)

/-- The forward discretization-unification comparison retains every underlying element. -/
theorem discretizationUnificationModels_hom_heq
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) (s)
    (x : ((heterogeneousDiscretizationModels sig h ⋙ unificationModels n sig).obj B).obj.obj.carrier s) :
    HEq (((((discretizationUnificationModels sig h).hom.app B).hom.hom.toMap s x).val).val) x.val.val :=
  inducedSquareModelsNatIso_hom_heq (unification n sig) (heterogeneousDiscretization sig h)
    (homogeneousDiscretization sig h) (unification m sig) _ _ _ _ _ _ _ _ _ _ _ _ B s x

/-- The inverse discretization-unification comparison retains every underlying element. -/
theorem discretizationUnificationModels_inv_heq
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) (s)
    (x : ((unificationModels m sig ⋙ homogeneousDiscretizationModels sig h).obj B).obj.obj.carrier s) :
    HEq (((((discretizationUnificationModels sig h).inv.app B).hom.hom.toMap s x).val).val) x.val.val :=
  inducedSquareModelsNatIso_inv_heq (unification n sig) (heterogeneousDiscretization sig h)
    (homogeneousDiscretization sig h) (unification m sig) _ _ _ _ _ _ _ _ _ _ _ _ B s x

/-- Discretization commutes with unification between categorial algebras.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def discretizationUnificationFunctor :
    heterogeneousDiscretizationFunctor.{u, v, w} sig h ⋙ unificationFunctor n sig ≅
      unificationFunctor m sig ⋙ homogeneousDiscretizationFunctor sig h :=
  conjugateSquareIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism (discretizationUnificationModels sig h)

end CategorialAlgebras.Dimensions
