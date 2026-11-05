import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.EqToHom

/-!
# Restriction and corestriction of functors

Restriction is composition with a full-subcategory inclusion. Corestriction uses
`ObjectProperty.lift`; it is the unique functor whose composite with the inclusion
is the original functor.
-/

universe u v u' v'

namespace CategorialAlgebras

open CategoryTheory

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

/-- Restriction of $F$ to the full subcategory on $P$. -/
abbrev restrict (F : C ⥤ D) (P : ObjectProperty C) : P.FullSubcategory ⥤ D := P.ι ⋙ F

/-- Corestriction of $F$ to the full subcategory on $P$. -/
abbrev corestrict (F : C ⥤ D) (P : ObjectProperty D) (h : ∀ X, P (F.obj X)) :
    C ⥤ P.FullSubcategory := P.lift F h

/-- Corestriction followed by inclusion recovers the original functor. -/
@[simp] theorem corestrict_comp_inclusion (F : C ⥤ D) (P : ObjectProperty D)
    (h : ∀ X, P (F.obj X)) : corestrict F P h ⋙ P.ι = F := rfl

/-- Postcomposition by a full-subcategory inclusion is injective on functors. -/
theorem inclusion_comp_injective (P : ObjectProperty D) :
    Function.Injective (fun L : C ⥤ P.FullSubcategory => L ⋙ P.ι) := by
  intro L M h
  have ho : ∀ X, L.obj X = M.obj X := fun X =>
    ObjectProperty.FullSubcategory.ext (congrArg (fun F : C ⥤ D => F.obj X) h)
  refine Functor.ext ho ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  have hm := Functor.congr_hom h f
  simpa using hm

/-- The functor with prescribed composite with the inclusion is unique. -/
theorem corestrict_unique (F : C ⥤ D) (P : ObjectProperty D)
    (h : ∀ X, P (F.obj X)) (L : C ⥤ P.FullSubcategory) (hL : L ⋙ P.ι = F) :
    L = corestrict F P h :=
  inclusion_comp_injective P (hL.trans (corestrict_comp_inclusion F P h).symm)

/-- A functor factors uniquely through the full subcategory whenever all values lie in it. -/
theorem exists_unique_corestrict (F : C ⥤ D) (P : ObjectProperty D)
    (h : ∀ X, P (F.obj X)) : ∃! L : C ⥤ P.FullSubcategory, L ⋙ P.ι = F :=
  ⟨corestrict F P h, rfl, fun L hL => corestrict_unique F P h L hL⟩

end CategorialAlgebras
