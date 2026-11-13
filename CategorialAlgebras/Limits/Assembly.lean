import CategorialAlgebras.Limits.Reconstruction
import CategorialAlgebras.Limits.Corollaries
import CategorialAlgebras.Limits.PresentedFamilies

/-!
# Projective limits of categorial algebras

Reconstruction uses the explicit union and diagonal carriers. The inverse
functors assemble compatible morphisms by full faithfulness. Equivalences of
presentations then give the universal property for categorial algebras.
-/

universe u v w x y z

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

/-- A fully faithful functor with specified object reconstructions gives an equivalence
whose inverse uses exactly those reconstructions. -/
noncomputable def reconstructionEquivalence {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{x} D] (P : C ⥤ D) (hP : P.FullyFaithful)
    (object : D → C) (comparison : ∀ A, P.obj (object A) ≅ A) : C ≌ D := by
  let Q : D ⥤ C :=
    { obj := object
      map f := hP.preimage ((comparison _).hom ≫ f ≫ (comparison _).inv)
      map_id A := hP.map_injective (by simp)
      map_comp f g := hP.map_injective (by simp) }
  let ε : Q ⋙ P ≅ 𝟭 D := NatIso.ofComponents comparison (by
    intro A B f
    simp [Q])
  let η : 𝟭 C ≅ P ⋙ Q := NatIso.ofComponents
    (fun A => hP.preimageIso (comparison (P.obj A)).symm) (by
      intro A B f
      apply hP.map_injective
      simp [Q, Functor.FullyFaithful.preimageIso])
  exact CategoryTheory.Equivalence.mk P Q η ε

variable {S : Type u} (sig : Signature.{u, v} S)

/-- The reconstructed homogeneous model, on the explicit increasing union. -/
noncomputable def homogeneousLimitModel (A : (homogeneousSystem.{u, v, w} sig).Family) :
    Homogeneous.OmegaModels.{u, v, w} sig :=
  let r := homogeneousReconstruction sig A
  ⟨⟨⟨homogeneousUnionPartial A, r.isModel.1⟩, r.isModel.2⟩, r.finiteCells⟩

/-- The reconstructed heterogeneous model, on the explicit diagonal carriers. -/
noncomputable def heterogeneousLimitModel (A : (heterogeneousSystem.{u, v, w} sig).Family) :
    (Heterogeneous.specification ℕ sig).Models.{u, max v u, w, 0} :=
  let r := heterogeneousReconstruction sig A
  ⟨⟨heterogeneousDiagonalPartial A, r.isModel.1⟩, r.isModel.2⟩

/-- The homogeneous model equivalence uses the explicit increasing union as its inverse. -/
noncomputable def homogeneousLimitEquivalence :
    Homogeneous.OmegaModels.{u, v, w} sig ≌ (homogeneousSystem.{u, v, w} sig).Family :=
  reconstructionEquivalence (homogeneousCone sig)
    (Functor.FullyFaithful.ofFullyFaithful (homogeneousCone sig))
    (homogeneousLimitModel sig) (fun A => (homogeneousReconstruction sig A).comparison)

/-- The heterogeneous model equivalence uses the explicit diagonal as its inverse. -/
noncomputable def heterogeneousLimitEquivalence :
    (Heterogeneous.specification ℕ sig).Models.{u, max v u, w, 0} ≌
      (heterogeneousSystem.{u, v, w} sig).Family :=
  reconstructionEquivalence (heterogeneousCone sig)
    (Functor.FullyFaithful.ofFullyFaithful (heterogeneousCone sig))
    (heterogeneousLimitModel sig) (fun A => (heterogeneousReconstruction sig A).comparison)

/-- Homogeneous $\omega$-categorial algebras are a projective limit up to isomorphism.

**Formally weaker** than the informal statement. Informally, the category is the projective limit of
the truncation functors, which compose strictly; here they compose up to natural isomorphisms that
are the identity on elements, so the universal property is stated up to these isomorphisms:
compatible families factor up to isomorphism, through a functor that is unique up to a unique
compatible isomorphism. -/
noncomputable def homogeneousProjectiveLimit :
    ProjectiveLimit (homogeneousSystem.{u, v, w} sig) (Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) where
  equivalence := Homogeneous.omegaModelIsomorphism.toEquivalence.trans
    (homogeneousLimitEquivalence sig)

/-- Heterogeneous $\omega$-categorial algebras are a projective limit up to isomorphism.

**Formally weaker** than the informal statement. Informally, the category is the projective limit of
the truncation functors, which compose strictly; here they compose up to natural isomorphisms that
are the identity on elements, so the universal property is stated up to these isomorphisms:
compatible families factor up to isomorphism, through a functor that is unique up to a unique
compatible isomorphism. -/
noncomputable def heterogeneousProjectiveLimit :
    ProjectiveLimit (heterogeneousSystem.{u, v, w} sig) (Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig) where
  equivalence := Heterogeneous.modelIsomorphism.toEquivalence.trans
    (heterogeneousLimitEquivalence sig)

/-- The homogeneous model reconstruction retains exactly the union carrier. -/
theorem homogeneousLimitModel_carrier (A : (homogeneousSystem.{u, v, w} sig).Family) :
    (homogeneousLimitModel sig A).obj.obj.obj.carrier = HomogeneousUnion A := rfl

/-- The heterogeneous model reconstruction retains exactly the diagonal carriers. -/
theorem heterogeneousLimitModel_carrier (A : (heterogeneousSystem.{u, v, w} sig).Family) :
    (heterogeneousLimitModel sig A).obj.obj.carrier = HeterogeneousDiagonal A := rfl

/-- The homogeneous finite algebra projection is the transported finite model projection. -/
noncomputable def homogeneousProjectionIso (n : ℕ) :
    (homogeneousProjectiveLimit.{u, v, w} sig).projection n ⋙ Homogeneous.modelIsomorphism.inverse ≅
      homogeneousOmegaTruncationFunctor sig n := eqToIso (by
    apply CategoryTheory.Functor.ext (fun A => rfl))

/-- The heterogeneous finite algebra projection is the transported finite model projection. -/
noncomputable def heterogeneousProjectionIso (n : ℕ) :
    (heterogeneousProjectiveLimit.{u, v, w} sig).projection n ⋙ Heterogeneous.modelIsomorphism.inverse ≅
      heterogeneousOmegaTruncationFunctor sig n := eqToIso (by
    apply CategoryTheory.Functor.ext (fun A => rfl))

variable {L : Type x} [Category.{y} L]

/-- The homogeneous functor induced by any coherent finite family. -/
noncomputable def homogeneousLift (F : (homogeneousSystem.{u, v, w} sig).FunctorFamily L) :
    L ⥤ Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig :=
  (homogeneousProjectiveLimit sig).lift F

/-- The heterogeneous functor induced by any coherent finite family. -/
noncomputable def heterogeneousLift (F : (heterogeneousSystem.{u, v, w} sig).FunctorFamily L) :
    L ⥤ Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig :=
  (heterogeneousProjectiveLimit sig).lift F

/-- The finite homogeneous truncations of the induced functor are the given finite functors. -/
noncomputable def homogeneousLiftFactor
    (F : (homogeneousSystem.{u, v, w} sig).FunctorFamily L) (n : ℕ) :
    homogeneousLift sig F ⋙ homogeneousOmegaTruncationFunctor sig n ≅
      F.functor n ⋙ Homogeneous.modelIsomorphism.inverse :=
  (Functor.isoWhiskerLeft (homogeneousLift sig F) (homogeneousProjectionIso sig n)).symm ≪≫
    Functor.isoWhiskerRight ((homogeneousProjectiveLimit sig).factorLevel F n)
      Homogeneous.modelIsomorphism.inverse

/-- The finite heterogeneous truncations of the induced functor are the given finite functors. -/
noncomputable def heterogeneousLiftFactor
    (F : (heterogeneousSystem.{u, v, w} sig).FunctorFamily L) (n : ℕ) :
    heterogeneousLift sig F ⋙ heterogeneousOmegaTruncationFunctor sig n ≅
      F.functor n ⋙ Heterogeneous.modelIsomorphism.inverse :=
  (Functor.isoWhiskerLeft (heterogeneousLift sig F) (heterogeneousProjectionIso sig n)).symm ≪≫
    Functor.isoWhiskerRight ((heterogeneousProjectiveLimit sig).factorLevel F n)
      Heterogeneous.modelIsomorphism.inverse
/-- Compatible finite homogeneous algebra functors, using their exact model presentations for coherence. -/
abbrev HomogeneousFunctorFamily (L : Type x) [Category.{y} L] :=
  PresentedFunctorFamily (homogeneousSystem.{u, v, w} sig)
    (fun n => Homogeneous.NCategorialAlgebra.{u, v, w} n sig) (fun _ => Homogeneous.modelIsomorphism) L

/-- Compatible finite heterogeneous algebra functors, using their exact model presentations for coherence. -/
abbrev HeterogeneousFunctorFamily (L : Type x) [Category.{y} L] :=
  PresentedFunctorFamily (heterogeneousSystem.{u, v, w} sig)
    (fun n => Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (fun _ => Heterogeneous.modelIsomorphism) L

/-- Assemble a coherent family of homogeneous algebra functors into dimension $\omega$. -/
noncomputable def homogeneousPresentedLift (F : HomogeneousFunctorFamily.{u, v, w} sig L) :
    L ⥤ Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig := homogeneousLift sig F.toModels

/-- Assemble a coherent family of heterogeneous algebra functors into dimension $\omega$. -/
noncomputable def heterogeneousPresentedLift (F : HeterogeneousFunctorFamily.{u, v, w} sig L) :
    L ⥤ Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig := heterogeneousLift sig F.toModels

/-- The assembled homogeneous algebra functor has exactly the prescribed finite restrictions up to isomorphism. -/
noncomputable def homogeneousPresentedFactor (F : HomogeneousFunctorFamily.{u, v, w} sig L) (n : ℕ) :
    homogeneousPresentedLift sig F ⋙ homogeneousOmegaTruncationFunctor sig n ≅ F.functor n :=
  homogeneousLiftFactor sig F.toModels n ≪≫ eqToIso (by
    change F.functor n ⋙ (Homogeneous.modelIsomorphism.functor ⋙ Homogeneous.modelIsomorphism.inverse) = _
    rw [← Homogeneous.modelIsomorphism.unit_eq, Functor.comp_id])

/-- The assembled heterogeneous algebra functor has exactly the prescribed finite restrictions up to isomorphism. -/
noncomputable def heterogeneousPresentedFactor (F : HeterogeneousFunctorFamily.{u, v, w} sig L) (n : ℕ) :
    heterogeneousPresentedLift sig F ⋙ heterogeneousOmegaTruncationFunctor sig n ≅ F.functor n :=
  heterogeneousLiftFactor sig F.toModels n ≪≫ eqToIso (by
    change F.functor n ⋙ (Heterogeneous.modelIsomorphism.functor ⋙ Heterogeneous.modelIsomorphism.inverse) = _
    rw [← Heterogeneous.modelIsomorphism.unit_eq, Functor.comp_id])

/-- A homogeneous algebra-family lift is unique up to a unique compatible natural isomorphism. -/
theorem homogeneousPresented_unique (F : HomogeneousFunctorFamily.{u, v, w} sig L)
    (G : L ⥤ Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (q : G ⋙ homogeneousRestrictions sig ≅ F.toModels.toFunctor) :
    ∃! i : G ≅ homogeneousPresentedLift sig F,
      Functor.isoWhiskerRight i (homogeneousRestrictions sig) ≪≫
        (homogeneousProjectiveLimit sig).factor F.toModels = q :=
  (homogeneousProjectiveLimit sig).unique_factor F.toModels G q

/-- A heterogeneous algebra-family lift is unique up to a unique compatible natural isomorphism. -/
theorem heterogeneousPresented_unique (F : HeterogeneousFunctorFamily.{u, v, w} sig L)
    (G : L ⥤ Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (q : G ⋙ heterogeneousRestrictions sig ≅ F.toModels.toFunctor) :
    ∃! i : G ≅ heterogeneousPresentedLift sig F,
      Functor.isoWhiskerRight i (heterogeneousRestrictions sig) ≪≫
        (heterogeneousProjectiveLimit sig).factor F.toModels = q :=
  (heterogeneousProjectiveLimit sig).unique_factor F.toModels G q

end CategorialAlgebras.Limits
