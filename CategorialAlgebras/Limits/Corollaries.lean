import CategorialAlgebras.Limits.HomogeneousMorphisms
import CategorialAlgebras.Limits.HeterogeneousMorphisms
import CategorialAlgebras.Limits.Universal

/-!
# Morphisms and natural transformations from finite truncations

The truncation cones are fully faithful independently of object reconstruction.
Their morphisms are exactly compatible families of finite homomorphisms. The
same holds for natural transformations, and invertibility is detected levelwise.
-/

universe u v w x y

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

variable {S : Type u} (sig : Signature.{u, v} S)

/-- The compatible truncations of a homogeneous $\omega$-categorial algebra. -/
noncomputable def homogeneousRestrictions : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤
    (homogeneousSystem.{u, v, w} sig).Family :=
  Homogeneous.omegaModelFunctor ⋙ homogeneousCone sig

/-- The compatible truncations of a heterogeneous $\omega$-categorial algebra. -/
noncomputable def heterogeneousRestrictions : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤
    (heterogeneousSystem.{u, v, w} sig).Family :=
  Heterogeneous.modelFunctor ⋙ heterogeneousCone sig

/-- The homogeneous algebra truncation cone is fully faithful. -/
noncomputable def homogeneousRestrictionsFullyFaithful :
    (homogeneousRestrictions.{u, v, w} sig).FullyFaithful := by
  have : (homogeneousCone.{u, v, w} sig).Full := homogeneousCone_full_proof
  exact Homogeneous.omegaModelFunctorFullyFaithful.comp
    (Functor.FullyFaithful.ofFullyFaithful (homogeneousCone sig))

/-- The heterogeneous algebra truncation cone is fully faithful. -/
noncomputable def heterogeneousRestrictionsFullyFaithful :
    (heterogeneousRestrictions.{u, v, w} sig).FullyFaithful := by
  have : (heterogeneousCone.{u, v, w} sig).Full := heterogeneousCone_full_proof
  exact Heterogeneous.modelFunctorFullyFaithful.comp
    (Functor.FullyFaithful.ofFullyFaithful (heterogeneousCone sig))

/-- Homogeneous homomorphisms are exactly compatible families of finite truncations. -/
noncomputable def homogeneousHomEquiv (A B : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :
    (A ⟶ B) ≃ ((homogeneousRestrictions sig).obj A ⟶ (homogeneousRestrictions sig).obj B) :=
  (homogeneousRestrictionsFullyFaithful sig).homEquiv

/-- Heterogeneous homomorphisms are exactly compatible families of finite truncations. -/
noncomputable def heterogeneousHomEquiv (A B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :
    (A ⟶ B) ≃ ((heterogeneousRestrictions sig).obj A ⟶ (heterogeneousRestrictions sig).obj B) :=
  (heterogeneousRestrictionsFullyFaithful sig).homEquiv

namespace ProjectiveSystem

variable {C : ℕ → Type u} [∀ n, Category.{v} (C n)] {T : ProjectiveSystem C}
variable {L : Type x} [Category.{y} L] (F G : L ⥤ T.Family)

/-- A family of finite natural transformations compatible with the restriction identifications. -/
structure LevelTransformation where
  /-- The natural transformation at each level. -/
  level : ∀ n, F ⋙ Family.evaluation T n ⟶ G ⋙ Family.evaluation T n
  /-- Each component commutes with the transition isomorphisms. -/
  coherence : ∀ X {m n} (h : m ≤ n),
    (T.truncation h).map ((level n).app X) ≫ ((G.obj X).transition h).hom =
      ((F.obj X).transition h).hom ≫ (level m).app X

/-- Assemble compatible finite natural transformations into a transformation of families. -/
def LevelTransformation.toNatTrans (α : LevelTransformation F G) : F ⟶ G where
  app X := ⟨fun n => (α.level n).app X, α.coherence X⟩
  naturality {X Y} f := by
    apply Family.Hom.ext
    funext n
    exact (α.level n).naturality f

/-- Transformations of families are exactly compatible families of finite natural transformations. -/
def levelTransformationEquiv : (F ⟶ G) ≃ LevelTransformation F G where
  toFun α :=
    { level n := Functor.whiskerRight α (Family.evaluation T n)
      coherence X {m n} h := (α.app X).comm h }
  invFun := LevelTransformation.toNatTrans F G
  left_inv α := by
    apply NatTrans.ext
    funext X
    apply Family.Hom.ext
    rfl
  right_inv α := by
    cases α
    rfl

end ProjectiveSystem

variable {L : Type x} [Category.{y} L]

/-- Homogeneous transformations are exactly coherent families of finite natural transformations. -/
noncomputable def homogeneousNatTransEquiv
    (F G : L ⥤ Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :
    (F ⟶ G) ≃ ProjectiveSystem.LevelTransformation
      (F ⋙ homogeneousRestrictions sig) (G ⋙ homogeneousRestrictions sig) :=
  ((homogeneousRestrictionsFullyFaithful sig).whiskeringRight L).homEquiv.trans
    (ProjectiveSystem.levelTransformationEquiv _ _)

/-- Heterogeneous transformations are exactly coherent families of finite natural transformations. -/
noncomputable def heterogeneousNatTransEquiv
    (F G : L ⥤ Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :
    (F ⟶ G) ≃ ProjectiveSystem.LevelTransformation
      (F ⋙ heterogeneousRestrictions sig) (G ⋙ heterogeneousRestrictions sig) :=
  ((heterogeneousRestrictionsFullyFaithful sig).whiskeringRight L).homEquiv.trans
    (ProjectiveSystem.levelTransformationEquiv _ _)

/-- Fully faithful family-valued functors detect invertibility at every finite level. -/
theorem isIso_of_finite_components {C : ℕ → Type u} [∀ n, Category.{v} (C n)]
    {T : ProjectiveSystem C} {D : Type w} [Category D] (P : D ⥤ T.Family)
    (hP : P.FullyFaithful) {F G : L ⥤ D} (α : F ⟶ G)
    (h : ∀ X n, IsIso ((P.map (α.app X)).app n)) : IsIso α := by
  have hi (X : L) : IsIso (P.map (α.app X)) := by
    let f := P.map (α.app X)
    let e := ProjectiveSystem.Family.isoMk T (fun n => asIso (f.app n)) (fun k => f.comm k)
    change IsIso e.hom
    infer_instance
  have : ∀ X, IsIso (α.app X) := fun X => by
    have := hi X
    exact hP.isIso_of_isIso_map (α.app X)
  exact NatIso.isIso_of_isIso_app α

/-- A homogeneous natural transformation is invertible if all its finite truncations are. -/
theorem homogeneous_isIso_of_components
    {F G : L ⥤ Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig} (α : F ⟶ G)
    (h : ∀ X n, IsIso (((homogeneousRestrictions sig).map (α.app X)).app n)) : IsIso α :=
  isIso_of_finite_components _ (homogeneousRestrictionsFullyFaithful sig) α h

/-- A heterogeneous natural transformation is invertible if all its finite truncations are. -/
theorem heterogeneous_isIso_of_components
    {F G : L ⥤ Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig} (α : F ⟶ G)
    (h : ∀ X n, IsIso (((heterogeneousRestrictions sig).map (α.app X)).app n)) : IsIso α :=
  isIso_of_finite_components _ (heterogeneousRestrictionsFullyFaithful sig) α h

end CategorialAlgebras.Limits
