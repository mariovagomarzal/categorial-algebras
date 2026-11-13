import CategorialAlgebras.Omega.GraduationLimit
import CategorialAlgebras.Omega.FamilyTransport

/-!
# Graduation induced from the original finite algebra functors

The finite functors in this family are exactly truncation followed by
graduation between categorial algebras. Their coherent model presentations
give the specified projective lift and its compatible uniqueness.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions Limits
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} (sig : Signature.{u, v} S)

/-- Expansion cancels the intermediate strict presentation isomorphisms. -/
noncomputable def finiteGraduationPresentationIso (n : ℕ) :
    (homogeneousOmegaTruncationFunctor.{u, v, w} sig n ⋙ Presentations.graduationFunctor n sig) ⋙
      Heterogeneous.modelIsomorphism.functor ≅ finiteGraduationModels sig n :=
  eqToIso (by
    change (Homogeneous.omegaModelIsomorphism.functor ⋙ homogeneousOmegaTruncationModels sig n) ⋙
      (Homogeneous.modelIsomorphism.inverse ⋙ Homogeneous.modelIsomorphism.functor) ⋙
        Presentations.graduationModels n sig ⋙
          (Heterogeneous.modelIsomorphism.inverse ⋙ Heterogeneous.modelIsomorphism.functor) = _
    rw [Homogeneous.modelIsomorphism.counit_eq, Heterogeneous.modelIsomorphism.counit_eq]
    rfl)

/-- The family of the original finite graduation functors after infinite truncation. -/
noncomputable def graduationPresentedFamily :
    HeterogeneousFunctorFamily.{u, v, w} sig (Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :=
  let F := transportFamily (graduationFamily sig)
    (fun n => (homogeneousOmegaTruncationFunctor sig n ⋙ Presentations.graduationFunctor n sig) ⋙
      Heterogeneous.modelIsomorphism.functor) (finiteGraduationPresentationIso sig)
  { functor n := homogeneousOmegaTruncationFunctor sig n ⋙ Presentations.graduationFunctor n sig
    transition := F.transition
    identity := F.identity
    coherence := F.coherence }

/-- Explicit graduation realizes the compatible family of the original finite algebra functors. -/
noncomputable def graduationPresentedComparison :
    graduationFunctor.{u, v, w} sig ⋙ heterogeneousRestrictions sig ≅
      (graduationPresentedFamily sig).toModels.toFunctor :=
  graduationFamilyComparison sig ≪≫ (transportFamilyComparison (graduationFamily sig)
    (fun n => (homogeneousOmegaTruncationFunctor sig n ⋙ Presentations.graduationFunctor n sig) ⋙
      Heterogeneous.modelIsomorphism.functor) (finiteGraduationPresentationIso sig)).symm

/-- Graduation induced by the projective property in the original algebra presentations. -/
noncomputable def presentedGraduationFunctor :
    Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤ Heterogeneous.OmegaCategorialAlgebra sig :=
  heterogeneousPresentedLift sig (graduationPresentedFamily sig)

/-- The prescribed finite algebra functors are the restrictions of the projective lift. -/
noncomputable def presentedGraduationFactor (n : ℕ) :
    presentedGraduationFunctor.{u, v, w} sig ⋙ heterogeneousOmegaTruncationFunctor sig n ≅
      homogeneousOmegaTruncationFunctor sig n ⋙ Presentations.graduationFunctor n sig :=
  heterogeneousPresentedFactor sig (graduationPresentedFamily sig) n

/-- The explicit graduation is the projectively induced functor up to a unique compatible isomorphism. -/
theorem graduation_unique_presented :
    ∃! i : graduationFunctor.{u, v, w} sig ≅ presentedGraduationFunctor sig,
      Functor.isoWhiskerRight i (heterogeneousRestrictions sig) ≪≫
        (heterogeneousProjectiveLimit sig).factor (graduationPresentedFamily sig).toModels =
          graduationPresentedComparison sig :=
  heterogeneousPresented_unique sig (graduationPresentedFamily sig) (graduationFunctor sig)
    (graduationPresentedComparison sig)

end CategorialAlgebras.Omega
