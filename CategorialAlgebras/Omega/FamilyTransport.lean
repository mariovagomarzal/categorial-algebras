import CategorialAlgebras.Limits.PresentedFamilies

/-!
# Transporting the levels of compatible functor families

Replacing every level by a naturally isomorphic functor transports both
transition maps and their coherences. This permits the original finite
algebra functors to be used with their exact model presentations.
-/

universe u v w x y z
namespace CategorialAlgebras.Omega
open CategoryTheory Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : ℕ → Type u} [∀ n, Category.{v} (C n)]
variable {T : ProjectiveSystem C} {L : Type w} [Category.{x} L]

/-- Replace every level of a coherent family by an isomorphic functor. -/
def transportFamily (F : T.FunctorFamily L) (g : ∀ n, L ⥤ C n)
    (i : ∀ n, g n ≅ F.functor n) : T.FunctorFamily L where
  functor := g
  transition {m n} h := Functor.isoWhiskerRight (i n) (T.truncation h) ≪≫
    F.transition h ≪≫ (i m).symm
  identity n X := by
    dsimp
    rw [F.identity]
    rw [← Category.assoc, (T.identity n).hom.naturality]
    simp only [Functor.id_map, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  coherence {m n p} h k X := by
    dsimp
    simp only [Functor.map_comp]
    calc
      _ = (T.truncation h).map ((T.truncation k).map ((i p).hom.app X)) ≫
          ((T.truncation h).map ((F.transition k).hom.app X) ≫ (F.transition h).hom.app X) ≫
            (i m).inv.app X := by
        have hc : (T.truncation h).map ((i n).inv.app X) ≫
            (T.truncation h).map ((i n).hom.app X) = 𝟙 _ := by
          rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
        simp only [Category.assoc]
        rw [← Category.assoc ((T.truncation h).map ((i n).inv.app X))
          ((T.truncation h).map ((i n).hom.app X)), hc, Category.id_comp]
      _ = (T.truncation h).map ((T.truncation k).map ((i p).hom.app X)) ≫
          ((T.composition h k).hom.app ((F.functor p).obj X) ≫
            (F.transition (le_trans h k)).hom.app X) ≫ (i m).inv.app X := by rw [F.coherence]
      _ = _ := by
        have hn := (T.composition h k).hom.naturality ((i p).hom.app X)
        dsimp only [Functor.comp_map] at hn
        simpa only [Category.assoc] using congrArg
          (fun f => f ≫ (F.transition (le_trans h k)).hom.app X ≫ (i m).inv.app X) hn

/-- The transported coherent family is naturally isomorphic to the original family. -/
def transportFamilyComparison (F : T.FunctorFamily L) (g : ∀ n, L ⥤ C n)
    (i : ∀ n, g n ≅ F.functor n) :
    (transportFamily F g i).toFunctor ≅ F.toFunctor :=
  NatIso.ofComponents (fun X => ProjectiveSystem.Family.isoMk T
    (fun n => (i n).app X) (by
      intro m n h
      change (T.truncation h).map ((i n).hom.app X) ≫ (F.transition h).hom.app X =
        ((T.truncation h).map ((i n).hom.app X) ≫ (F.transition h).hom.app X ≫
          (i m).inv.app X) ≫ (i m).hom.app X
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id])) (by
    intro X Y f
    apply ProjectiveSystem.Family.Hom.ext
    funext n
    exact (i n).hom.naturality f)

end CategorialAlgebras.Omega
