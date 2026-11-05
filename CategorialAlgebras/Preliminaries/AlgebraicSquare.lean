import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Algebraic squares

Four adjunctions form an algebraic square when their left composites and their right
composites are naturally isomorphic. Conjugation of the left comparison supplies a
canonical right comparison, with the units and counits of the composite adjunctions.
-/

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategorialAlgebras

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
variable {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
variable {J : C ⥤ C'} {K : C' ⥤ C} {H : D ⥤ D'} {I : D' ⥤ D}

/-- An algebraic square of four adjunctions, with both natural comparisons.
The comparisons need not be conjugate; the canonical conjugate is supplied separately. -/
structure AlgebraicSquare (a : F ⊣ G) (a' : F' ⊣ G') (b : J ⊣ K) (c : H ⊣ I) where
  /-- Comparison of the two composites of left adjoints. -/
  leftIso : J ⋙ F' ≅ F ⋙ H
  /-- Comparison of the two composites of right adjoints. -/
  rightIso : I ⋙ G ≅ G' ⋙ K

namespace AlgebraicSquare

variable (a : F ⊣ G) (a' : F' ⊣ G') (b : J ⊣ K) (c : H ⊣ I)

/-- The right comparison conjugate to $\alpha$ under the composite adjunctions. -/
def conjugateIso (α : J ⋙ F' ≅ F ⋙ H) : I ⋙ G ≅ G' ⋙ K :=
  conjugateIsoEquiv (a.comp c) (b.comp a') α

/-- The right comparison is precisely the conjugate of the left comparison. -/
theorem conjugateIso_hom (α : J ⋙ F' ≅ F ⋙ H) :
    (conjugateIso a a' b c α).hom =
      conjugateEquiv (a.comp c) (b.comp a') α.hom := rfl

/-- Component formula: first the composite unit, then the transported comparison,
then the transported composite counit. -/
theorem conjugateIso_hom_app (α : J ⋙ F' ≅ F ⋙ H) (Y : D') :
    (conjugateIso a a' b c α).hom.app Y =
      (b.comp a').unit.app ((I ⋙ G).obj Y) ≫
        (G' ⋙ K).map (α.hom.app ((I ⋙ G).obj Y)) ≫
        (G' ⋙ K).map ((a.comp c).counit.app Y) := by
  simp [conjugateIso, conjugateEquiv_apply_app]

/-- A left comparison completes four adjunctions to an algebraic square. -/
def ofLeftIso (α : J ⋙ F' ≅ F ⋙ H) : AlgebraicSquare a a' b c where
  leftIso := α
  rightIso := conjugateIso a a' b c α

end AlgebraicSquare
end CategorialAlgebras
