import CategorialAlgebras.Omega.Adjunctions
import CategorialAlgebras.Omega.Equivalence
import CategorialAlgebras.Omega.UnificationCompatibility
import CategorialAlgebras.Preliminaries.AlgebraicSquare

/-!
# The algebraic square between finite dimensions and dimension $\omega$

The comparison on right adjoints is the dimensional injection into classes.
Conjugation is a bijection of natural isomorphisms, so it determines the
unique comparison of left adjoints and the four-adjunction square.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
variable {S : Type u} (sig : Signature.{u, v} S) (m : ℕ)

/-- The comparison of left adjoints determined uniquely by the dimensional injection. -/
noncomputable def discretizationGraduationFunctor :
    homogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⋙ graduationFunctor sig ≅
      Presentations.graduationFunctor m sig ⋙ heterogeneousOmegaDiscretizationFunctor sig m :=
  (conjugateIsoEquiv ((Presentations.presentationAdjunction m sig).comp (heterogeneousAdjunction sig m))
    ((homogeneousAdjunction sig m).comp (presentationAdjunction sig))).symm
      (truncationUnificationFunctor sig m)

/-- The left comparison first inserts the composite unit, applies the class injection,
and then applies the composite counit. -/
theorem discretizationGraduationFunctor_hom_app
    (A : Homogeneous.NCategorialAlgebra.{u, v, w} m sig) :
    (discretizationGraduationFunctor sig m).hom.app A =
      (homogeneousOmegaDiscretizationFunctor sig m ⋙ graduationFunctor sig).map
        (((Presentations.presentationAdjunction m sig).comp (heterogeneousAdjunction sig m)).unit.app A) ≫
      (homogeneousOmegaDiscretizationFunctor sig m ⋙ graduationFunctor sig).map
        ((truncationUnificationFunctor sig m).hom.app
          ((Presentations.graduationFunctor m sig ⋙ heterogeneousOmegaDiscretizationFunctor sig m).obj A)) ≫
      (((homogeneousAdjunction sig m).comp (presentationAdjunction sig)).counit.app
        ((Presentations.graduationFunctor m sig ⋙ heterogeneousOmegaDiscretizationFunctor sig m).obj A)) := by
  simp [discretizationGraduationFunctor, conjugateIsoEquiv, conjugateEquiv, mateEquiv]

/-- The left comparison on an individual cell is the unit, class injection and counit formula. -/
theorem discretizationGraduationFunctor_hom_apply
    (A : Homogeneous.NCategorialAlgebra.{u, v, w} m sig) (s : S) (k : ℕ)
    (x : (((homogeneousOmegaDiscretizationFunctor sig m ⋙ graduationFunctor sig).obj A).sort s).carrier k) :
    (((discretizationGraduationFunctor sig m).hom.app A).sort s).toFun k x =
      (((((homogeneousAdjunction sig m).comp (presentationAdjunction sig)).counit.app
          ((Presentations.graduationFunctor m sig ⋙ heterogeneousOmegaDiscretizationFunctor sig m).obj A)).sort s).toFun k)
        (((((homogeneousOmegaDiscretizationFunctor sig m ⋙ graduationFunctor sig).map
          ((truncationUnificationFunctor sig m).hom.app
            ((Presentations.graduationFunctor m sig ⋙ heterogeneousOmegaDiscretizationFunctor sig m).obj A))).sort s).toFun k)
          (((((homogeneousOmegaDiscretizationFunctor sig m ⋙ graduationFunctor sig).map
            (((Presentations.presentationAdjunction m sig).comp (heterogeneousAdjunction sig m)).unit.app A)).sort s).toFun k) x)) :=
  congrArg (fun f => (f.sort s).toFun k x) (discretizationGraduationFunctor_hom_app sig m A)

/-- The dimensional injection comparison is exactly the conjugate of the left comparison. -/
theorem truncationUnificationFunctor_eq_conjugate :
    truncationUnificationFunctor.{u, v, w} sig m =
      AlgebraicSquare.conjugateIso (Presentations.presentationAdjunction m sig) (presentationAdjunction sig)
        (homogeneousAdjunction sig m) (heterogeneousAdjunction sig m)
        (discretizationGraduationFunctor sig m) := by
  exact ((conjugateIsoEquiv
    ((Presentations.presentationAdjunction m sig).comp (heterogeneousAdjunction sig m))
    ((homogeneousAdjunction sig m).comp (presentationAdjunction sig))).apply_symm_apply _).symm

/-- The four specified adjunctions and their natural comparisons form an algebraic square.

**Formally weaker** than the informal statement. Informally, the natural isomorphism $\alpha$ of
this square and the units of its adjunctions are identities; here they are natural isomorphisms that
are the identity on elements, since the carriers of transformed algebras are subtypes of cells. -/
noncomputable def dimensionAlgebraicSquare :
    AlgebraicSquare (Presentations.presentationAdjunction.{u, v, w} m sig) (presentationAdjunction sig)
      (homogeneousAdjunction sig m) (heterogeneousAdjunction sig m) where
  leftIso := discretizationGraduationFunctor sig m
  rightIso := truncationUnificationFunctor sig m

/-- The dimension square is the canonical square obtained from its left comparison. -/
theorem dimensionAlgebraicSquare_eq_ofLeftIso :
    dimensionAlgebraicSquare.{u, v, w} sig m =
      AlgebraicSquare.ofLeftIso (Presentations.presentationAdjunction m sig) (presentationAdjunction sig)
        (homogeneousAdjunction sig m) (heterogeneousAdjunction sig m)
        (discretizationGraduationFunctor sig m) := by
  change AlgebraicSquare.mk _ (truncationUnificationFunctor sig m) = AlgebraicSquare.mk _ _
  rw [truncationUnificationFunctor_eq_conjugate]

/-- The left comparison is uniquely determined by its prescribed conjugate. -/
theorem discretizationGraduationFunctor_unique
    (α : homogeneousOmegaDiscretizationFunctor.{u, v, w} sig m ⋙ graduationFunctor sig ≅
      Presentations.graduationFunctor m sig ⋙ heterogeneousOmegaDiscretizationFunctor sig m)
    (hα : AlgebraicSquare.conjugateIso (Presentations.presentationAdjunction m sig) (presentationAdjunction sig)
      (homogeneousAdjunction sig m) (heterogeneousAdjunction sig m) α = truncationUnificationFunctor sig m) :
    α = discretizationGraduationFunctor sig m := by
  apply (conjugateIsoEquiv
    ((Presentations.presentationAdjunction m sig).comp (heterogeneousAdjunction sig m))
    ((homogeneousAdjunction sig m).comp (presentationAdjunction sig))).injective
  exact hα.trans (truncationUnificationFunctor_eq_conjugate sig m)

end CategorialAlgebras.Omega
