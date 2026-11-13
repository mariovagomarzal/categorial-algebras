import CategorialAlgebras.Dimensions.UnificationCompatibility
import CategorialAlgebras.Dimensions.DiscretizationUnification
import CategorialAlgebras.Dimensions.SquareTransport

/-!
# The algebraic square of finite dimension changes

Graduation and unification, together with discretization and truncation in
both presentations, form an algebraic square. Its right comparison is the
conjugate of its left comparison. The remaining graduation-truncation and
unification-discretization squares commute by their canonical comparisons.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S : Type u} (sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n)

/-- The unification-truncation comparison is the conjugate of the graduation-discretization comparison. -/
theorem truncationUnificationFunctor_eq_conjugate :
    truncationUnificationFunctor.{u, v, w} sig h =
      AlgebraicSquare.conjugateIso (presentationAdjunction m sig) (presentationAdjunction n sig)
        (homogeneousAdjunction sig h) (heterogeneousAdjunction sig h)
        (discretizationGraduationFunctor sig h) :=
  conjugateSquareIso_conjugateIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    (modelPresentationAdjunction m sig) (modelPresentationAdjunction n sig)
    (homogeneousModelAdjunction sig h) (heterogeneousModelAdjunction sig h)
    (discretizationGraduationModels sig h)

/-- The four finite-dimensional adjunctions, with their specified natural comparisons.

**Formally weaker** than the informal statement. Informally, the natural isomorphism $\alpha$ of
this square and the units of its adjunctions are identities; here they are natural isomorphisms that
are the identity on elements, since the carriers of transformed algebras are subtypes of cells. -/
noncomputable def dimensionAlgebraicSquare :
    AlgebraicSquare (presentationAdjunction.{u, v, w} m sig) (presentationAdjunction n sig)
      (homogeneousAdjunction sig h) (heterogeneousAdjunction sig h) where
  leftIso := discretizationGraduationFunctor sig h
  rightIso := truncationUnificationFunctor sig h

/-- The dimension square is precisely the canonical square obtained from its left comparison. -/
theorem dimensionAlgebraicSquare_eq_ofLeftIso :
    dimensionAlgebraicSquare.{u, v, w} sig h =
      AlgebraicSquare.ofLeftIso (presentationAdjunction m sig) (presentationAdjunction n sig)
        (homogeneousAdjunction sig h) (heterogeneousAdjunction sig h)
        (discretizationGraduationFunctor sig h) := by
  change AlgebraicSquare.mk _ (truncationUnificationFunctor sig h) = AlgebraicSquare.mk _ _
  rw [truncationUnificationFunctor_eq_conjugate]

/-- The other two mixed squares also commute, with the canonical identifications already constructed. -/
noncomputable def dimensionMixedComparisons :
    (graduationFunctor.{u, v, w} n sig ⋙ heterogeneousTruncationFunctor sig h ≅
      homogeneousTruncationFunctor sig h ⋙ graduationFunctor m sig) ×
    (heterogeneousDiscretizationFunctor sig h ⋙ unificationFunctor n sig ≅
      unificationFunctor m sig ⋙ homogeneousDiscretizationFunctor sig h) :=
  ⟨truncationGraduationFunctor sig h, discretizationUnificationFunctor sig h⟩

end CategorialAlgebras.Dimensions
