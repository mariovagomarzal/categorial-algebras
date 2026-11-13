import CategorialAlgebras.Omega.HomogeneousCounit
import CategorialAlgebras.Omega.HeterogeneousCounit

/-!
# Infinite discretization is left adjoint to finite truncation

The unit retains every element, while the homogeneous counit is inclusion of
cutoff cells and the heterogeneous counit consists of dimensional identities.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} (sig : Signature.{u, v} S) (m : ℕ)

/-- The homogeneous counit is a monomorphism because it is inclusion on elements. -/
theorem homogeneousCounit_mono (B : Homogeneous.OmegaModels.{u, v, w} sig) :
    Mono ((homogeneousCounit (sig := sig) m).app B) := by
  have hi : ∀ s, Function.Injective
      (((homogeneousCounit (sig := sig) m).app B).hom.hom.hom.toMap s) := by
    intro s x y he
    apply Subtype.ext
    apply Subtype.ext
    exact (homogeneousCounitPartial_val m B.obj.obj.obj ⟨B.obj.obj.property, B.obj.property⟩ s x).symm.trans
      (he.trans (homogeneousCounitPartial_val m B.obj.obj.obj ⟨B.obj.obj.property, B.obj.property⟩ s y))
  constructor
  intro Z f g he
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply PartialAlgebra.Hom.ext
  funext s x
  exact hi s (congrArg (fun q : Z ⟶ B => q.hom.hom.hom.toMap s x) he)

/-- The explicit homogeneous unit and inclusion counit satisfy the forward triangle. -/
theorem homogeneous_left_triangle (B : (Homogeneous.specification (Fin m) sig).Models) :
    (homogeneousOmegaDiscretizationModels.{u, v, w} sig m).map
        ((homogeneousRoundTripModels sig m).inv.app B) ≫
      (homogeneousCounit m).app ((homogeneousOmegaDiscretizationModels sig m).obj B) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply PartialAlgebra.Hom.ext
  funext s x
  apply Subtype.ext
  let DB := (homogeneousOmegaDiscretizationModels sig m).obj B
  change ((homogeneousCounitPartial m DB.obj.obj.obj ⟨DB.obj.obj.property, DB.obj.property⟩).toMap s _).val = x.val
  erw [homogeneousCounitPartial_val]
  exact homogeneousRoundTripModels_inv_val sig m B s x.val

/-- Homogeneous discretization is left adjoint to homogeneous truncation on models. -/
noncomputable def homogeneousModelAdjunction :
    homogeneousOmegaDiscretizationModels.{u, v, w} sig m ⊣ homogeneousOmegaTruncationModels sig m :=
  adjunctionOfUnitIsoCounitMono (homogeneousRoundTripModels sig m).symm
    (homogeneousCounit m) (homogeneousCounit_mono sig m) (homogeneous_left_triangle sig m)

/-- The homogeneous model unit is identity on underlying elements. -/
theorem homogeneousModelAdjunction_unit_val
    (B : (Homogeneous.specification (Fin m) sig).Models) (s : S) (x : B.obj.obj.carrier s) :
    ((((homogeneousModelAdjunction sig m).unit.app B).hom.hom.toMap s x).val.val) = x :=
  homogeneousRoundTripModels_inv_val sig m B s x

/-- The homogeneous model counit is exactly the specified inclusion. -/
theorem homogeneousModelAdjunction_counit :
    (homogeneousModelAdjunction.{u, v, w} sig m).counit = homogeneousCounit m := rfl

/-- The homogeneous adjunction transported to categorial algebras.

**Formally weaker** than the informal statement. Informally, the unit of this adjunction is the
identity; here it is the inverse of a natural isomorphism that is the identity on elements, since
the carriers of transformed algebras are subtypes of cells. -/
noncomputable def homogeneousAdjunction :
    homogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⊣ homogeneousOmegaTruncationFunctor sig m :=
  Homogeneous.modelIsomorphism.toEquivalence.toAdjunction.comp
    ((homogeneousModelAdjunction sig m).comp Homogeneous.omegaModelIsomorphism.symm.toEquivalence.toAdjunction)


/-- The heterogeneous counit is monomorphic because every identity inclusion is injective. -/
theorem heterogeneousCounit_mono (B : (Heterogeneous.specification ℕ sig).Models) :
    Mono ((heterogeneousCounit (sig := sig) m).app B) := by
  apply model_mono_of_injective
  intro p x y he
  rcases p with ⟨k, s⟩
  apply Subtype.ext
  apply Subtype.ext
  change (heterogeneousCounitPartial m B.obj.obj _).toMap (k, s) x =
    (heterogeneousCounitPartial m B.obj.obj _).toMap (k, s) y at he
  erw [heterogeneousCounitPartial_val, heterogeneousCounitPartial_val] at he
  exact Function.LeftInverse.injective (dimensionLE _ (counitDimension_le m k)).source_identity he

/-- The heterogeneous identity inclusions satisfy the forward triangle. -/
theorem heterogeneous_left_triangle
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) :
    (heterogeneousOmegaDiscretizationModels.{u, v, w} sig m).map
        ((heterogeneousRoundTripModels sig m).inv.app B) ≫
      (heterogeneousCounit m).app ((heterogeneousOmegaDiscretizationModels sig m).obj B) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply PartialAlgebra.Hom.ext
  funext p x
  rcases p with ⟨k, s⟩
  apply Subtype.ext
  let DB := (heterogeneousOmegaDiscretizationModels sig m).obj B
  change ((heterogeneousCounitPartial m DB.obj.obj ⟨DB.obj.property, DB.property⟩).toMap (k, s) _).val = x.val
  erw [heterogeneousCounitPartial_val]
  apply eq_of_heq
  apply HEq.trans (heterogeneousDiscretization_identity_val m B.obj.obj
    ⟨B.obj.property, B.property⟩ (counitDimension_le m k)
    (omegaClamp_counitDimension m k) s _)
  exact heterogeneousRoundTripModels_inv_val sig m B (omegaClamp m k, s) x.val

/-- Heterogeneous discretization is left adjoint to heterogeneous truncation on models. -/
noncomputable def heterogeneousModelAdjunction :
    heterogeneousOmegaDiscretizationModels.{u, v, w} sig m ⊣ heterogeneousOmegaTruncationModels sig m :=
  adjunctionOfUnitIsoCounitMono (heterogeneousRoundTripModels sig m).symm
    (heterogeneousCounit m) (heterogeneousCounit_mono sig m) (heterogeneous_left_triangle sig m)

/-- The heterogeneous model unit is identity on elements, with its canonical sort transport. -/
theorem heterogeneousModelAdjunction_unit_val
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) (p) (x : B.obj.obj.carrier p) :
    HEq ((((heterogeneousModelAdjunction sig m).unit.app B).hom.hom.toMap p x).val.val) x :=
  heterogeneousRoundTripModels_inv_val sig m B p x

/-- The heterogeneous model counit is exactly the specified family of identity inclusions. -/
theorem heterogeneousModelAdjunction_counit :
    (heterogeneousModelAdjunction.{u, v, w} sig m).counit = heterogeneousCounit m := rfl

/-- The heterogeneous adjunction transported to categorial algebras.

**Formally weaker** than the informal statement. Informally, the unit of this adjunction is the
identity; here it is the inverse of a natural isomorphism that is the identity on elements, since
the carriers of transformed algebras are subtypes of cells. -/
noncomputable def heterogeneousAdjunction :
    heterogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⊣ heterogeneousOmegaTruncationFunctor sig m :=
  Heterogeneous.modelIsomorphism.toEquivalence.toAdjunction.comp
    ((heterogeneousModelAdjunction sig m).comp Heterogeneous.modelIsomorphism.symm.toEquivalence.toAdjunction)

end CategorialAlgebras.Omega
