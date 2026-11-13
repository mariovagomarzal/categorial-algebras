import CategorialAlgebras.Presentations.CompositeDerivors
import CategorialAlgebras.Presentations.GraduationModels
import CategorialAlgebras.Presentations.UnificationModels
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The relation between graduation and unification

The comparison of induced transformations identifies the homogeneous round trip with
identity. The heterogeneous round trip identifies each cell with its top identity.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- The homogeneous round trip is identified with the original model using the composition
comparison, equality of generalized derivors, and the identity transformation. -/
noncomputable def homogeneousRoundTripIso
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    (unification n sig).transformed ((graduation n sig).transformed B) ≅ B :=
  (unification n sig).comparisonIso (graduation n sig) B
    ((unification n sig).comparison_surjective_of_empty (graduation n sig) B (fun _ => rfl))
    (unification_isModel n sig _ (graduation_isModel n sig B hB)).1 ≪≫
    eqToIso (congrArg (fun c => GeneralizedHepDerivor.transformed c B)
      (unification_comp_graduation n sig)) ≪≫
    (GeneralizedHepDerivor.identityIso (sig := Homogeneous.hepSignature (Fin n) sig) B
      (EPSignature.IsEPAlgebra.isWeak hB.1)).symm

/-- The homogeneous round-trip identification is the identity on underlying elements. -/
@[simp] theorem homogeneousRoundTripIso_hom
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) (s : S)
    (x : (unification n sig).Cell ((graduation n sig).transformed B) s) :
    (homogeneousRoundTripIso n sig B hB).hom.toMap s x = x.val.val := by
  exact eq_of_heq (transformed_transport_val (unification_comp_graduation n sig) B s
    (((unification n sig).comparison (graduation n sig) B).toMap s x)
    (congrArg (fun c => GeneralizedHepDerivor.transformed c B)
      (unification_comp_graduation n sig)))

/-- Graduation followed by unification is naturally isomorphic to identity on models. -/
noncomputable def homogeneousRoundTrip : graduationModels.{u, v, w} n sig ⋙
    unificationModels n sig ≅ 𝟭 _ :=
  NatIso.ofComponents (fun B => modelIso _ _
    (homogeneousRoundTripIso n sig B.obj.obj ⟨B.obj.property, B.property⟩)) (by
      intro B C f
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply PartialAlgebra.Hom.ext
      funext s x
      exact (homogeneousRoundTripIso_hom n sig C.obj.obj ⟨C.obj.property, C.property⟩ s _).trans
        (congrArg (f.hom.hom.toMap s) (homogeneousRoundTripIso_hom n sig B.obj.obj
          ⟨B.obj.property, B.property⟩ s x).symm))

end CategorialAlgebras.Presentations
