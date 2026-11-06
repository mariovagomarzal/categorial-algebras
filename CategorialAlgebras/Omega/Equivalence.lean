import CategorialAlgebras.Omega.Zeta
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The adjoint equivalence of natural-dimensional presentations

Graduation and unification are mutually inverse up to their explicit natural
isomorphisms. The adjunction uses exactly $\zeta^{-1}$ as unit and
$\theta^{-1}$ as counit, with both triangular identities.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} (sig : Signature.{u, v} S)

/-- Graduating the homogeneous unit gives the heterogeneous injection comparison. -/
theorem graduation_unit_eq_theta (A : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :
    (graduationFunctor sig).map ((zeta sig).inv.app A) =
      (theta sig).hom.app ((graduationFunctor sig).obj A) := by
  apply Heterogeneous.CategorialAlgebra.Hom.ext
  funext s
  apply Heterogeneous.Functor.ext
  funext k x
  apply Subtype.ext
  exact zeta_inv_cell A k s x

/-- The equivalence with its prescribed unit and counit and the forward triangle verified. -/
noncomputable def presentationEquivalence :
    Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig ≌
      Heterogeneous.OmegaCategorialAlgebra sig where
  functor := graduationFunctor sig
  inverse := unificationFunctor sig
  unitIso := (zeta sig).symm
  counitIso := (theta sig).symm
  functor_unitIso_comp A := by
    change (graduationFunctor sig).map ((zeta sig).inv.app A) ≫
      (theta sig).inv.app ((graduationFunctor sig).obj A) = _
    rw [graduation_unit_eq_theta]
    exact (theta sig).hom_inv_id_app _

/-- Graduation is left adjoint to unification with the explicit unit and counit. -/
noncomputable def presentationAdjunction :
    graduationFunctor.{u, v, w} sig ⊣ unificationFunctor sig :=
  (presentationEquivalence sig).toAdjunction

/-- The unit is precisely the inverse of the homogeneous comparison. -/
theorem presentationAdjunction_unit :
    (presentationAdjunction.{u, v, w} sig).unit = (zeta sig).inv := rfl

/-- The counit is precisely the inverse of the heterogeneous comparison. -/
theorem presentationAdjunction_counit :
    (presentationAdjunction.{u, v, w} sig).counit = (theta sig).inv := rfl

/-- The forward triangular identity holds for the explicit comparisons. -/
theorem presentation_left_triangle (A : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :
    (graduationFunctor sig).map ((zeta sig).inv.app A) ≫
      (theta sig).inv.app ((graduationFunctor sig).obj A) = 𝟙 _ :=
  (presentationAdjunction sig).left_triangle_components A

/-- The backward triangular identity holds for the explicit comparisons. -/
theorem presentation_right_triangle (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :
    (zeta sig).inv.app ((unificationFunctor sig).obj B) ≫
      (unificationFunctor sig).map ((theta sig).inv.app B) = 𝟙 _ :=
  (presentationAdjunction sig).right_triangle_components B

/-- Both transformations of the presentation adjunction are invertible. -/
theorem presentationAdjunction_isIso :
    IsIso (presentationAdjunction.{u, v, w} sig).unit ∧
      IsIso (presentationAdjunction.{u, v, w} sig).counit := by
  change IsIso (zeta sig).inv ∧ IsIso (theta sig).inv
  constructor <;> infer_instance

/-- Graduation is an equivalence in the sense of Mathlib. -/
instance graduationFunctor_isEquivalence : (graduationFunctor.{u, v, w} sig).IsEquivalence :=
  (presentationEquivalence sig).isEquivalence_functor

/-- Unification is an equivalence in the sense of Mathlib. -/
instance unificationFunctor_isEquivalence : (unificationFunctor.{u, v, w} sig).IsEquivalence :=
  (presentationEquivalence sig).isEquivalence_inverse

end CategorialAlgebras.Omega
