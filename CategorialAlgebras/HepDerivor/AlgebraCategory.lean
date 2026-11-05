import CategorialAlgebras.HepDerivor.Comparison
import CategorialAlgebras.Preliminaries.Grothendieck

/-!
# The indexed and total categories of ep-algebras

Weak ep-algebras form a contravariant lax indexed category with invertible units.
The units add or remove cell proofs, and composition comparisons are inclusions.
The full subcategory of its Grothendieck construction on ep-algebras gives the
category of ep-algebras and generalized hep-derivor homomorphisms.
-/

universe u v w

namespace CategorialAlgebras

open CategoryTheory

namespace GeneralizedHepDerivor

variable {S T U : Type u} {sig : HepSignature.{u, v} S}
variable {tau : HepSignature.{u, v} T} {ups : HepSignature.{u, v} U}

/-- The comparison restricted and corestricted to weak ep-algebras. -/
noncomputable def weakComparison (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) :
    weakFunctor.{u, v, u, v, w} d ⋙ c.weakFunctor ⟶ (c.comp d).weakFunctor where
  app C := ObjectProperty.homMk (c.comparison d C.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ (c.comparison_naturality d f.hom)

/-- Equality transport between reindexings of the same derivor does not change
underlying elements. The heterogeneous equality retains the possible change of sort. -/
theorem weak_transport_val {c c' : GeneralizedHepDerivor sig tau} (h : c = c')
    (B : EPSignature.WEPAlg.{u, v, w} tau.toEPSignature) (s : S) (x : c.Cell B.obj s)
    (p : c.weakFunctor.obj B = c'.weakFunctor.obj B) :
    HEq (((eqToHom p).hom.toMap s x).val) x.val := by
  cases h
  rfl

end GeneralizedHepDerivor

namespace BundledHepSignature

/-- Weak ep-algebras indexed by hierarchical signatures. The unit is the canonical
identity on elements, realized as an isomorphism because carriers are cell subtypes. -/
noncomputable def weakAlgebras : LaxIndexedCategory (BundledHepSignature.{u, v}) where
  fiber sig := Cat.of (EPSignature.WEPAlg.{u, v, w} sig.signature.toEPSignature)
  map c := c.weakFunctor
  mapId sig := GeneralizedHepDerivor.weakIdentityIso sig.signature
  mapComp c d := c.weakComparison d
  mapComp_id_left c B := by
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext s x
    apply Subtype.ext
    exact (eq_of_heq (GeneralizedHepDerivor.weak_transport_val
      (GeneralizedHepDerivor.identity_comp c).symm B s x _)).symm
  mapComp_id_right c B := by
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext s x
    apply Subtype.ext
    exact (eq_of_heq (GeneralizedHepDerivor.weak_transport_val
      (GeneralizedHepDerivor.comp_identity c).symm B s x _)).symm
  mapComp_assoc c d e C := by
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext s x
    apply Subtype.ext
    exact (eq_of_heq (GeneralizedHepDerivor.weak_transport_val
      (GeneralizedHepDerivor.comp_assoc c d e) C s
      (((c.comp d).comparison e C.obj).toMap s
        ((c.comparison d (e.transformed C.obj)).toMap s x)) _)).symm

end BundledHepSignature
-- The total category combines sort, symbol and carrier universes through a maximum.
set_option linter.checkUnivs false in
/-- The total category of weak ep-algebras and generalized hep-derivor homomorphisms. -/
abbrev WeakHepAlgebra := (BundledHepSignature.weakAlgebras.{u, v, w}).Grothendieck

set_option linter.checkUnivs false in
/-- The category of ep-algebras, as a full subcategory of the total weak-algebra category. -/
abbrev HepAlgebra := ObjectProperty.FullSubcategory
  (fun X : WeakHepAlgebra.{u, v, w} => X.base.signature.IsEPAlgebra X.fiber.obj)

namespace WeakHepAlgebra

/-- Projection of a weak ep-algebra to its hierarchical signature. -/
noncomputable abbrev projection : WeakHepAlgebra.{u, v, w} ⥤ BundledHepSignature.{u, v} :=
  LaxIndexedCategory.Grothendieck.projection

end WeakHepAlgebra

namespace HepAlgebra

/-- The inclusion of ep-algebras into the total weak-algebra category. -/
noncomputable def inclusion : HepAlgebra.{u, v, w} ⥤ WeakHepAlgebra.{u, v, w} := ObjectProperty.ι _

/-- The inclusion of total-category ep-algebras is fully faithful. -/
noncomputable def inclusionFullyFaithful : (inclusion.{u, v, w}).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- Projection of an ep-algebra to its hierarchical signature. -/
noncomputable def projection : HepAlgebra.{u, v, w} ⥤ BundledHepSignature.{u, v} :=
  inclusion ⋙ WeakHepAlgebra.projection

/-- Package an ep-algebra and its hierarchical signature into the total category. -/
def ofEPAlg (sig : BundledHepSignature.{u, v})
    (A : EPSignature.EPAlg.{u, v, w} sig.signature.toEPSignature) : HepAlgebra.{u, v, w} :=
  ⟨⟨sig, ⟨A.obj, EPSignature.IsEPAlgebra.isWeak (sig := sig.signature.toEPSignature)
    A.property⟩⟩, A.property⟩

/-- The underlying generalized hep-derivor of a total-category morphism. -/
abbrev base {A B : HepAlgebra.{u, v, w}} (f : A ⟶ B) :
    A.obj.base ⟶ B.obj.base := f.hom.base

/-- The partial-algebra homomorphism component of a total-category morphism. -/
abbrev fiber {A B : HepAlgebra.{u, v, w}} (f : A ⟶ B) :
    A.obj.fiber.obj ⟶ (base f).transformed B.obj.fiber.obj := f.hom.fiber.hom

/-- Form a total-category morphism from a generalized hep-derivor and a homomorphism
to its transformed target algebra. -/
noncomputable def homMk {A B : HepAlgebra.{u, v, w}} (c : A.obj.base ⟶ B.obj.base)
    (f : A.obj.fiber.obj ⟶ c.transformed B.obj.fiber.obj) : A ⟶ B :=
  ObjectProperty.homMk ⟨c, ObjectProperty.homMk f⟩

/-- Identities project to identity generalized hep-derivors. -/
@[simp] theorem id_base (A : HepAlgebra.{u, v, w}) : base (𝟙 A) = 𝟙 A.obj.base := rfl

/-- The identity homomorphism component adds only the unrestricted cell proof. -/
@[simp] theorem id_fiber (A : HepAlgebra.{u, v, w}) : fiber (𝟙 A) =
    GeneralizedHepDerivor.identityLift A.obj.fiber.obj A.obj.fiber.property := rfl

/-- The base of a composite is the composite generalized hep-derivor. -/
@[simp] theorem comp_base {A B C : HepAlgebra.{u, v, w}} (f : A ⟶ B) (g : B ⟶ C) :
    base (f ≫ g) = base f ≫ base g := rfl

/-- Composition first applies the first homomorphism, then the reindexed second
homomorphism, and finally the comparison inclusion $\kappa$. -/
@[simp] theorem comp_fiber {A B C : HepAlgebra.{u, v, w}} (f : A ⟶ B) (g : B ⟶ C) :
    fiber (f ≫ g) = fiber f ≫ (base f).transformedHom (fiber g) ≫
      (base f).comparison (base g) C.obj.fiber.obj := rfl

end HepAlgebra
end CategorialAlgebras
