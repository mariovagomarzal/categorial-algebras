import CategorialAlgebras.Dimensions.HomogeneousCounit
import CategorialAlgebras.Dimensions.HeterogeneousCounit
import CategorialAlgebras.Dimensions.Transport
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Discretization is left adjoint to truncation

The units insert the selected-cell proofs and retain every element. The
counits are the inclusions already constructed. Their injectivity lets the
second triangle follow categorically from the first triangle and naturality.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory

/-- An invertible unit, a monomorphic counit and the forward triangle determine an adjunction. -/
noncomputable def adjunctionOfUnitIsoCounitMono {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    (hm : ∀ Y, Mono (ε.app Y))
    (hl : ∀ X, F.map (η.hom.app X) ≫ ε.app (F.obj X) = 𝟙 (F.obj X)) : F ⊣ G := by
  letI : F.Faithful :=
    { map_injective := fun {X Y} f g he => by
        apply (cancel_mono (η.hom.app Y)).1
        erw [η.hom.naturality f, η.hom.naturality g]
        exact congrArg (fun k => η.hom.app X ≫ G.map k) he }
  refine
    { unit := η.hom
      counit := ε
      left_triangle_components := hl
      right_triangle_components := ?_ }
  intro Y
  have := hm Y
  apply F.map_injective
  rw [F.map_comp, F.map_id]
  apply (cancel_mono (ε.app Y)).1
  change (F.map (η.hom.app (G.obj Y)) ≫ (G ⋙ F).map (ε.app Y)) ≫ ε.app Y = _
  erw [Category.assoc, ε.naturality (ε.app Y), ← Category.assoc, hl, Category.id_comp]

/-- Sortwise injectivity of a model homomorphism implies that it is a monomorphism. -/
theorem model_mono_of_injective {S : Type u} {sig : EPSignature.{u, v} S}
    {E : EPSpecification sig} {B C : E.Models} (f : B ⟶ C)
    (hf : ∀ s, Function.Injective (f.hom.hom.toMap s)) : Mono f := by
  constructor
  intro Z g h he
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply PartialAlgebra.Hom.ext
  funext s x
  apply hf s
  exact congrArg (fun q : Z ⟶ C => q.hom.hom.toMap s x) he

variable {S : Type u} (sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n)

/-- The homogeneous counit is a monomorphism because it is inclusion on elements. -/
theorem homogeneousCounit_mono (B : (Homogeneous.specification (Fin n) sig).Models) :
    Mono ((homogeneousCounit (sig := sig) h).app B) := by
  apply model_mono_of_injective
  intro s x y he
  apply Subtype.ext
  apply Subtype.ext
  exact (homogeneousCounitPartial_val h B.obj.obj ⟨B.obj.property, B.property⟩ s x).symm.trans
    (he.trans (homogeneousCounitPartial_val h B.obj.obj ⟨B.obj.property, B.property⟩ s y))

/-- The explicit homogeneous unit and inclusion counit satisfy the forward triangle. -/
theorem homogeneous_left_triangle (B : (Homogeneous.specification (Fin m) sig).Models) :
    (homogeneousDiscretizationModels.{u, v, w} sig h).map
        ((homogeneousRoundTripModels sig h).inv.app B) ≫
      (homogeneousCounit h).app ((homogeneousDiscretizationModels sig h).obj B) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply PartialAlgebra.Hom.ext
  funext s x
  apply Subtype.ext
  let DB := (homogeneousDiscretizationModels sig h).obj B
  change ((homogeneousCounitPartial h DB.obj.obj ⟨DB.obj.property, DB.property⟩).toMap s _).val = x.val
  erw [homogeneousCounitPartial_val]
  exact eq_of_heq (homogeneousRoundTripModels_inv_val sig h B s x.val)

/-- Homogeneous discretization is left adjoint to homogeneous truncation on models. -/
noncomputable def homogeneousModelAdjunction :
    homogeneousDiscretizationModels.{u, v, w} sig h ⊣ homogeneousTruncationModels sig h :=
  adjunctionOfUnitIsoCounitMono (homogeneousRoundTripModels sig h).symm
    (homogeneousCounit h) (homogeneousCounit_mono sig h) (homogeneous_left_triangle sig h)

/-- The homogeneous model unit is identity on underlying elements. -/
theorem homogeneousModelAdjunction_unit_val
    (B : (Homogeneous.specification (Fin m) sig).Models) (s : S) (x : B.obj.obj.carrier s) :
    ((((homogeneousModelAdjunction sig h).unit.app B).hom.hom.toMap s x).val.val) = x :=
  eq_of_heq (homogeneousRoundTripModels_inv_val sig h B s x)

/-- The homogeneous model counit is exactly the specified inclusion. -/
theorem homogeneousModelAdjunction_counit :
    (homogeneousModelAdjunction.{u, v, w} sig h).counit = homogeneousCounit h := rfl

/-- The homogeneous adjunction transported to categorial algebras. -/
noncomputable def homogeneousAdjunction :
    homogeneousDiscretizationFunctor.{u, v, w} sig h ⊣ homogeneousTruncationFunctor sig h :=
  Homogeneous.modelIsomorphism.toEquivalence.toAdjunction.comp
    ((homogeneousModelAdjunction sig h).comp Homogeneous.modelIsomorphism.symm.toEquivalence.toAdjunction)


/-- The heterogeneous counit is monomorphic because every identity inclusion is injective. -/
theorem heterogeneousCounit_mono (B : (Heterogeneous.specification (Fin (n + 1)) sig).Models) :
    Mono ((heterogeneousCounit (sig := sig) h).app B) := by
  apply model_mono_of_injective
  intro p x y he
  rcases p with ⟨k, s⟩
  apply Subtype.ext
  apply Subtype.ext
  change (heterogeneousCounitPartial h B.obj.obj _).toMap (k, s) x =
    (heterogeneousCounitPartial h B.obj.obj _).toMap (k, s) y at he
  erw [heterogeneousCounitPartial_val, heterogeneousCounitPartial_val] at he
  exact Function.LeftInverse.injective (dimensionLE _ (counitDimension_le h k)).source_identity he

/-- The heterogeneous identity inclusions satisfy the forward triangle. -/
theorem heterogeneous_left_triangle
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) :
    (heterogeneousDiscretizationModels.{u, v, w} sig h).map
        ((heterogeneousRoundTripModels sig h).inv.app B) ≫
      (heterogeneousCounit h).app ((heterogeneousDiscretizationModels sig h).obj B) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply PartialAlgebra.Hom.ext
  funext p x
  rcases p with ⟨k, s⟩
  apply Subtype.ext
  let DB := (heterogeneousDiscretizationModels sig h).obj B
  change ((heterogeneousCounitPartial h DB.obj.obj ⟨DB.obj.property, DB.property⟩).toMap (k, s) _).val = x.val
  erw [heterogeneousCounitPartial_val]
  apply eq_of_heq
  apply HEq.trans (heterogeneousDiscretization_identity_val h B.obj.obj
    ⟨B.obj.property, B.property⟩ (counitDimension_le h k)
    (clampDimension_inclusion h (clampDimension m k)) s _)
  exact heterogeneousRoundTripModels_inv_val sig h B (clampDimension m k, s) x.val

/-- Heterogeneous discretization is left adjoint to heterogeneous truncation on models. -/
noncomputable def heterogeneousModelAdjunction :
    heterogeneousDiscretizationModels.{u, v, w} sig h ⊣ heterogeneousTruncationModels sig h :=
  adjunctionOfUnitIsoCounitMono (heterogeneousRoundTripModels sig h).symm
    (heterogeneousCounit h) (heterogeneousCounit_mono sig h) (heterogeneous_left_triangle sig h)

/-- The heterogeneous model unit is identity on elements, with its canonical sort transport. -/
theorem heterogeneousModelAdjunction_unit_val
    (B : (Heterogeneous.specification (Fin (m + 1)) sig).Models) (p) (x : B.obj.obj.carrier p) :
    HEq ((((heterogeneousModelAdjunction sig h).unit.app B).hom.hom.toMap p x).val.val) x :=
  heterogeneousRoundTripModels_inv_val sig h B p x

/-- The heterogeneous model counit is exactly the specified family of identity inclusions. -/
theorem heterogeneousModelAdjunction_counit :
    (heterogeneousModelAdjunction.{u, v, w} sig h).counit = heterogeneousCounit h := rfl

/-- The heterogeneous adjunction transported to categorial algebras. -/
noncomputable def heterogeneousAdjunction :
    heterogeneousDiscretizationFunctor.{u, v, w} sig h ⊣ heterogeneousTruncationFunctor sig h :=
  Heterogeneous.modelIsomorphism.toEquivalence.toAdjunction.comp
    ((heterogeneousModelAdjunction sig h).comp Heterogeneous.modelIsomorphism.symm.toEquivalence.toAdjunction)

end CategorialAlgebras.Dimensions
