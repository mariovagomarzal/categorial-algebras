import CategorialAlgebras.Omega.GraduationFamily

/-!
# Graduation and the projective universal property

The explicit graduated algebra has the prescribed compatible finite
restrictions. Thus it is canonically identified with the functor induced
by the heterogeneous projective limit, uniquely with its specified factors.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} (sig : Signature.{u, v} S)

/-- The finite restriction comparison, naturally in the homogeneous algebra. -/
noncomputable def graduationRestrictionModels (n : ℕ) :
    graduationFunctor.{u, v, w} sig ⋙ Heterogeneous.modelFunctor ⋙
      heterogeneousOmegaTruncationModels sig n ≅ finiteGraduationModels sig n :=
  NatIso.ofComponents (fun A => Presentations.modelIso _ _ (graduationRestrictionPartial A.obj n)) (by
    intro A B f
    apply model_hom_ext
    intro p x
    apply Subtype.ext
    apply Subtype.ext
    exact (graduationRestrictionPartial_hom_val B.obj n p _).trans
      (congrArg (f.hom.sort p.2).toFun (graduationRestrictionPartial_hom_val A.obj n p x)).symm)

/-- Graduation commutes naturally with the existing finite truncation functors. -/
noncomputable def truncationGraduationFunctor (n : ℕ) :
    graduationFunctor.{u, v, w} sig ⋙ heterogeneousOmegaTruncationFunctor sig n ≅
      homogeneousOmegaTruncationFunctor sig n ⋙ Presentations.graduationFunctor n sig :=
  Functor.isoWhiskerRight (graduationRestrictionModels sig n) Heterogeneous.modelIsomorphism.inverse ≪≫
    eqToIso (by
      change Homogeneous.omegaModelIsomorphism.functor ⋙ homogeneousOmegaTruncationModels sig n ⋙
        Presentations.graduationModels n sig ⋙ Heterogeneous.modelIsomorphism.inverse =
        (Homogeneous.omegaModelIsomorphism.functor ⋙ homogeneousOmegaTruncationModels sig n) ⋙
          (Homogeneous.modelIsomorphism.inverse ⋙ Homogeneous.modelIsomorphism.functor) ⋙
            Presentations.graduationModels n sig ⋙ Heterogeneous.modelIsomorphism.inverse
      rw [Homogeneous.modelIsomorphism.counit_eq]
      rfl)

/-- The explicit graduation gives the entire compatible family, not only its objects. -/
noncomputable def graduationFamilyComparison :
    graduationFunctor.{u, v, w} sig ⋙ heterogeneousRestrictions sig ≅
      (graduationFamily sig).toFunctor :=
  NatIso.ofComponents (fun A => ProjectiveSystem.Family.isoMk _
    (fun n => (graduationRestrictionModels sig n).app A) (by
      intro m n h
      apply model_hom_ext
      intro p x
      apply Subtype.ext
      apply Subtype.ext
      change (((graduationTransition sig h).hom.app A).hom.hom.toMap p
        (((heterogeneousTruncationModels sig h).map
          ((graduationRestrictionModels sig n).hom.app A)).hom.hom.toMap p x)).val.val =
        (((graduationRestrictionModels sig m).hom.app A).hom.hom.toMap p
          (((heterogeneousOmegaTruncationModelsComp sig h).hom.app
            ((graduatedAlgebra A.obj).toModel)).hom.hom.toMap p x)).val.val
      rw [graduationTransition_val]
      change ((graduationRestrictionPartial A.obj n).hom.toMap _ x.val).val.val =
        ((graduationRestrictionPartial A.obj m).hom.toMap p
          (((heterogeneousOmegaTruncationModelsComp sig h).hom.app
            ((graduatedAlgebra A.obj).toModel)).hom.hom.toMap p x)).val.val
      rw [graduationRestrictionPartial_hom_val, graduationRestrictionPartial_hom_val]
      exact (congrArg Subtype.val (eq_of_heq (heterogeneousCone_heq sig h
        ((graduatedAlgebra A.obj).toModel) p x))).symm)) (by
    intro A B f
    apply ProjectiveSystem.Family.Hom.ext
    funext n
    exact (graduationRestrictionModels sig n).hom.naturality f)

/-- The graduation obtained by the projective universal property. -/
noncomputable def inducedGraduationFunctor :
    Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤ Heterogeneous.OmegaCategorialAlgebra sig :=
  heterogeneousLift sig (graduationFamily sig)

/-- The explicit graduation is the induced graduation up to the unique compatible isomorphism.

**Formally weaker** than the informal statement. Informally, the graduation functor is the unique
functor whose truncations are the finite graduations; here it is unique up to a unique compatible
isomorphism, since the truncation functors compose only up to isomorphism. -/
theorem graduation_unique_induced :
    ∃! i : graduationFunctor.{u, v, w} sig ≅ inducedGraduationFunctor sig,
      Functor.isoWhiskerRight i (heterogeneousRestrictions sig) ≪≫
        (heterogeneousProjectiveLimit sig).factor (graduationFamily sig) = graduationFamilyComparison sig :=
  (heterogeneousProjectiveLimit sig).unique_factor (graduationFamily sig)
    (graduationFunctor sig) (graduationFamilyComparison sig)

/-- Every other specified factorization is uniquely isomorphic to explicit graduation. -/
theorem graduation_unique
    (G : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤ Heterogeneous.OmegaCategorialAlgebra sig)
    (q : G ⋙ heterogeneousRestrictions sig ≅ (graduationFamily sig).toFunctor) :
    ∃! i : G ≅ graduationFunctor sig,
      Functor.isoWhiskerRight i (heterogeneousRestrictions sig) ≪≫ graduationFamilyComparison sig = q := by
  let ff := (heterogeneousRestrictionsFullyFaithful sig).whiskeringRight
    (Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
  let i := ff.preimageIso (q ≪≫ (graduationFamilyComparison sig).symm)
  have hi : Functor.isoWhiskerRight i (heterogeneousRestrictions sig) =
      q ≪≫ (graduationFamilyComparison sig).symm := by
    apply Iso.ext
    exact ff.map_preimage _
  have hh : Functor.isoWhiskerRight i (heterogeneousRestrictions sig) ≪≫ graduationFamilyComparison sig = q := by
    rw [hi]
    simp
  refine ⟨i, hh, ?_⟩
  intro j hj
  apply Iso.ext
  apply ff.map_injective
  apply (cancel_mono (graduationFamilyComparison sig).hom).mp
  exact (congrArg Iso.hom hj).trans
    (congrArg Iso.hom hh).symm

end CategorialAlgebras.Omega
