import CategorialAlgebras.Limits.ProjectiveSystem
import Mathlib.CategoryTheory.IsoCat

/-!
# Compatible families in isomorphic presentations

Finite categories can be replaced by their strict model presentations. The
functors of a compatible family may be given in the original categories;
only their coherence diagrams are expressed through the presentation functors.
-/

universe u v w x y z
namespace CategorialAlgebras.Limits
open CategoryTheory
variable {C : ℕ → Type u} [∀ n, Category.{v} (C n)]
variable (T : ProjectiveSystem C)
variable (B : ℕ → Type w) [∀ n, Category.{x} (B n)] (e : ∀ n, IsoCat (B n) (C n))

/-- A coherent family of functors in categories isomorphic to the stages of a projective system. -/
structure PresentedFunctorFamily (L : Type y) [Category.{z} L] where
  /-- The finite functors, in their original presentations. -/
  functor : ∀ n, L ⥤ B n
  /-- Compatibility isomorphisms after expansion into the stage categories. -/
  transition : ∀ {m n} (h : m ≤ n),
    (functor n ⋙ (e n).functor) ⋙ T.truncation h ≅ functor m ⋙ (e m).functor
  /-- The identity compatibility agrees with the canonical one. -/
  identity : ∀ n X, (transition (le_refl n)).hom.app X =
    (T.identity n).hom.app (((functor n) ⋙ (e n).functor).obj X)
  /-- Compatibility respects the canonical composition isomorphisms. -/
  coherence : ∀ {m n p} (h : m ≤ n) (k : n ≤ p) X,
    (T.truncation h).map ((transition k).hom.app X) ≫ (transition h).hom.app X =
      (T.composition h k).hom.app (((functor p) ⋙ (e p).functor).obj X) ≫
        (transition (le_trans h k)).hom.app X

/-- Expand a compatible original family into the model-stage family. -/
def PresentedFunctorFamily.toModels {L : Type y} [Category.{z} L]
    (F : PresentedFunctorFamily T B e L) : T.FunctorFamily L where
  functor n := F.functor n ⋙ (e n).functor
  transition := F.transition
  identity := F.identity
  coherence := F.coherence

/-- Transport an original truncation comparison to the stage presentation. -/
noncomputable def presentedTransition {L : Type y} [Category.{z} L]
    {m n} (h : m ≤ n) {F : L ⥤ B n} {G : L ⥤ B m}
    (i : F ⋙ ((e n).functor ⋙ T.truncation h ⋙ (e m).inverse) ≅ G) :
    (F ⋙ (e n).functor) ⋙ T.truncation h ≅ G ⋙ (e m).functor :=
  eqToIso (by
    change F ⋙ (e n).functor ⋙ T.truncation h =
      F ⋙ (e n).functor ⋙ T.truncation h ⋙ ((e m).inverse ⋙ (e m).functor)
    rw [(e m).counit_eq, Functor.comp_id]) ≪≫ Functor.isoWhiskerRight i (e m).functor

end CategorialAlgebras.Limits
