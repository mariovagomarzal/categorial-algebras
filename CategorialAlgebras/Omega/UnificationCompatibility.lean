import CategorialAlgebras.Omega.FiniteUnification
import CategorialAlgebras.Presentations.Equivalence
import CategorialAlgebras.Limits.Truncations

/-!
# Unification commutes with finite truncation

The comparison is the dimensional injection into quotient classes. It is
natural, and its component formula is stated on the exact induced model carriers.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} (sig : Signature.{u, v} S) (n : ℕ)

/-- The finite unification comparison on models of the original heterogeneous algebras. -/
noncomputable def truncationUnificationModels :
    Heterogeneous.modelFunctor ⋙ heterogeneousOmegaTruncationModels.{u, v, w} sig n ⋙
      Presentations.unificationModels n sig ≅
    unificationFunctor sig ⋙ Homogeneous.omegaModelFunctor ⋙ homogeneousOmegaTruncationModels sig n :=
  NatIso.ofComponents (fun B => Presentations.modelIso _ _ (truncationUnificationPartial B n)) (by
    intro B C f
    apply Limits.model_hom_ext
    intro s x
    apply Subtype.ext
    change ((truncationUnificationPartial C n).hom.toMap s _).val =
      unifiedMap f s ((truncationUnificationPartial B n).hom.toMap s x).val
    rw [truncationUnificationPartial_hom_val, truncationUnificationPartial_hom_val]
    rfl)

/-- The natural comparison sends each representative $x$ to $[x]_n$. -/
theorem truncationUnificationModels_hom_val
    (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig) (s : S) (x) :
    (((truncationUnificationModels sig n).hom.app B).hom.hom.toMap s x).val =
      cellIn B n s x.val.val :=
  truncationUnificationPartial_hom_val B n s x

/-- Truncating heterogeneous algebras and unifying is naturally unifying and truncating. -/
noncomputable def truncationUnificationFunctor :
    heterogeneousOmegaTruncationFunctor.{u, v, w} sig n ⋙ Presentations.unificationFunctor n sig ≅
      unificationFunctor sig ⋙ homogeneousOmegaTruncationFunctor sig n :=
  eqToIso (by
    change (Heterogeneous.modelIsomorphism.functor ⋙ heterogeneousOmegaTruncationModels sig n) ⋙
      (Heterogeneous.modelIsomorphism.inverse ⋙ Heterogeneous.modelIsomorphism.functor) ⋙
        Presentations.unificationModels n sig ⋙ Homogeneous.modelIsomorphism.inverse = _
    rw [Heterogeneous.modelIsomorphism.counit_eq]
    rfl) ≪≫ Functor.isoWhiskerRight (truncationUnificationModels sig n) Homogeneous.modelIsomorphism.inverse

end CategorialAlgebras.Omega
