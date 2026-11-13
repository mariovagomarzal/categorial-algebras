import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Opposites

/-!
# Lax indexed categories and the Grothendieck construction

A lax indexed category assigns a category to each base object and a contravariant
reindexing functor to each base arrow. Its composition comparison need not be invertible.
Units may be natural isomorphisms. Strict normal data remain available as a special
case with equality units. The coherence law includes transport along base associativity.

The total category has arrows $(\varphi,f)$ with $f : x \to F_\varphi(y)$.
Split indexed categories are ordinary functors to $\mathsf{Cat}$ on the opposite base.
-/

universe u v u₁ v₁

namespace CategorialAlgebras

open CategoryTheory Opposite

variable (I : Type u) [Category.{v} I]

/-- A contravariant category assignment with invertible units and coherent lax
composition. The unit identifies each object with its identity reindexing. -/
structure LaxIndexedCategory where
  /-- The category over each base object. -/
  fiber : I → Cat.{v₁, u₁}
  /-- Contravariant reindexing along a base arrow. -/
  map : ∀ {i j}, (i ⟶ j) → (fiber j ⥤ fiber i)
  /-- The invertible unit of reindexing. -/
  mapId : ∀ i, 𝟭 (fiber i) ≅ map (𝟙 i)
  /-- The comparison from successive reindexing to composite reindexing. -/
  mapComp : ∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), map g ⋙ map f ⟶ map (f ≫ g)
  /-- Compatibility of the comparison with the unit at the source. -/
  mapComp_id_left : ∀ {i j} (f : i ⟶ j) (x : fiber j),
    (mapId i).hom.app ((map f).obj x) ≫ (mapComp (𝟙 i) f).app x =
      eqToHom (by rw [Category.id_comp]; rfl)
  /-- Compatibility of the comparison with the unit at the target. -/
  mapComp_id_right : ∀ {i j} (f : i ⟶ j) (x : fiber j),
    (map f).map ((mapId j).hom.app x) ≫ (mapComp f (𝟙 j)).app x =
      eqToHom (by rw [Category.comp_id]; rfl)
  /-- Associativity of comparisons, transported along associativity in the base. -/
  mapComp_assoc : ∀ {i j k l} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) (x : fiber l),
    (map f).map ((mapComp g h).app x) ≫ (mapComp f (g ≫ h)).app x =
      (mapComp f g).app ((map h).obj x) ≫ (mapComp (f ≫ g) h).app x ≫
        eqToHom (by rw [Category.assoc])

namespace LaxIndexedCategory

variable {I} (F : LaxIndexedCategory.{u, v, u₁, v₁} I)

/-- An object of the total category: a base object and an object of its fiber. -/
structure Grothendieck where
  /-- The base object. -/
  base : I
  /-- The object in the fiber. -/
  fiber : F.fiber base

namespace Grothendieck

variable {F}

/-- An arrow of the total category, given by a base arrow and a reindexed fiber arrow. -/
structure Hom (X Y : F.Grothendieck) where
  /-- The base arrow. -/
  base : X.base ⟶ Y.base
  /-- The arrow to the reindexed target. -/
  fiber : X.fiber ⟶ (F.map base).obj Y.fiber

/-- Extensionality with transport of the fiber codomain along the base equality. -/
@[ext (iff := false)] theorem Hom.ext {X Y : F.Grothendieck} (f g : Hom X Y)
    (hb : f.base = g.base)
    (hf : f.fiber ≫ eqToHom (by rw [hb]) = g.fiber) : f = g := by
  cases f
  cases g
  dsimp at hb hf
  subst hb
  simpa using hf

/-- Identity in the total category, using the invertible unit. -/
def id (X : F.Grothendieck) : Hom X X where
  base := 𝟙 X.base
  fiber := (F.mapId X.base).hom.app X.fiber

/-- Composition in the total category, with the lax comparison after reindexing. -/
def comp {X Y Z : F.Grothendieck} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber := f.fiber ≫ (F.map f.base).map g.fiber ≫ (F.mapComp f.base g.base).app Z.fiber

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The lax coherence and unit laws make the total construction a category. -/
instance : Category F.Grothendieck where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := by
    apply Hom.ext _ _ (Category.id_comp _)
    dsimp [comp, id]
    rw [← (F.mapId _).hom.naturality_assoc]
    rw [F.mapComp_id_left]
    simp
  comp_id f := by
    apply Hom.ext _ _ (Category.comp_id _)
    dsimp [comp, id]
    rw [F.mapComp_id_right]
    simp
  assoc f g h := by
    apply Hom.ext _ _ (Category.assoc _ _ _)
    dsimp [comp]
    simp only [Functor.map_comp, Category.assoc]
    rw [← (F.mapComp f.base g.base).naturality_assoc]
    rw [← F.mapComp_assoc]
    rfl

/-- The base component of an identity is the base identity. -/
@[simp] theorem id_base (X : F.Grothendieck) : (𝟙 X : X ⟶ X).base = 𝟙 X.base := rfl

/-- The fiber component of an identity is the component of the unit isomorphism. -/
@[simp] theorem id_fiber (X : F.Grothendieck) :
    (𝟙 X : X ⟶ X).fiber = (F.mapId X.base).hom.app X.fiber := rfl

/-- Composition projects to composition in the base. -/
@[simp] theorem comp_base {X Y Z : F.Grothendieck} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

/-- The explicit fiber formula for composition in the total category. -/
@[simp] theorem comp_fiber {X Y Z : F.Grothendieck} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫ (F.map f.base).map g.fiber ≫ (F.mapComp f.base g.base).app Z.fiber := rfl

/-- The projection from the total category to its base. -/
def projection : F.Grothendieck ⥤ I where
  obj X := X.base
  map f := f.base

end Grothendieck
end LaxIndexedCategory

/-- A contravariant category assignment with strict units and coherent lax composition.
`mapComp f g` has components $F_f(F_g(x)) \to F_{f\,\gg\,g}(x)$.
All equality transformations below transport only along equalities of functors or base arrows. -/
structure NormalLaxIndexedCategory where
  /-- The category over each base object. -/
  fiber : I → Cat.{v₁, u₁}
  /-- Contravariant reindexing along a base arrow. -/
  map : ∀ {i j}, (i ⟶ j) → (fiber j ⥤ fiber i)
  /-- Reindexing along an identity is the identity functor. -/
  map_id : ∀ i, map (𝟙 i) = 𝟭 (fiber i)
  /-- The lax comparison from iterated reindexing to composite reindexing. -/
  mapComp : ∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), map g ⋙ map f ⟶ map (f ≫ g)
  /-- The comparison with an identity first arrow is an equality transformation. -/
  mapComp_id_left : ∀ {i j} (f : i ⟶ j),
    mapComp (𝟙 i) f = eqToHom (by rw [map_id]; simp only [Category.id_comp]; rfl)
  /-- The comparison with an identity second arrow is an equality transformation. -/
  mapComp_id_right : ∀ {i j} (f : i ⟶ j),
    mapComp f (𝟙 j) = eqToHom (by rw [map_id]; simp only [Category.comp_id]; rfl)
  /-- Associativity of the lax comparisons, transported along base associativity. -/
  mapComp_assoc : ∀ {i j k l} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) (x : fiber l),
    (map f).map ((mapComp g h).app x) ≫ (mapComp f (g ≫ h)).app x =
      (mapComp f g).app ((map h).obj x) ≫ (mapComp (f ≫ g) h).app x ≫
        eqToHom (by rw [Category.assoc])

namespace NormalLaxIndexedCategory

variable {I} (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I)

/-- An object of the total category: a base object and an object of its fiber. -/
structure Grothendieck where
  /-- The base object. -/
  base : I
  /-- The object in the fiber. -/
  fiber : F.fiber base

namespace Grothendieck

variable {F}

/-- An arrow of the total category, given by a base arrow and a reindexed fiber arrow. -/
structure Hom (X Y : F.Grothendieck) where
  /-- The base arrow. -/
  base : X.base ⟶ Y.base
  /-- The arrow to the reindexed target. -/
  fiber : X.fiber ⟶ (F.map base).obj Y.fiber

/-- Extensionality with transport of the fiber codomain along the base equality. -/
@[ext (iff := false)] theorem Hom.ext {X Y : F.Grothendieck} (f g : Hom X Y)
    (hb : f.base = g.base)
    (hf : f.fiber ≫ eqToHom (by rw [hb]) = g.fiber) : f = g := by
  cases f
  cases g
  dsimp at hb hf
  subst hb
  simpa using hf

/-- Identity in the total category, using normality to identify its fiber codomain. -/
def id (X : F.Grothendieck) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by rw [F.map_id]; rfl)

/-- Composition in the total category, with the lax comparison after reindexing. -/
def comp {X Y Z : F.Grothendieck} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber := f.fiber ≫ (F.map f.base).map g.fiber ≫ (F.mapComp f.base g.base).app Z.fiber

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The lax coherence and normality laws make the total construction a category. -/
instance : Category F.Grothendieck where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := by
    apply Hom.ext _ _ (Category.id_comp _)
    dsimp [comp, id]
    simp only [F.mapComp_id_left, eqToHom_app, Category.assoc]
    rw [Functor.congr_hom (F.map_id _) f.fiber]
    simp [Category.assoc]
  comp_id f := by
    apply Hom.ext _ _ (Category.comp_id _)
    dsimp [comp, id]
    simp [F.mapComp_id_right, eqToHom_app, eqToHom_map]
  assoc f g h := by
    apply Hom.ext _ _ (Category.assoc _ _ _)
    dsimp [comp]
    simp only [Functor.map_comp, Category.assoc]
    rw [← (F.mapComp f.base g.base).naturality_assoc]
    rw [← F.mapComp_assoc]
    rfl

/-- The base component of an identity is the base identity. -/
@[simp] theorem id_base (X : F.Grothendieck) : (𝟙 X : X ⟶ X).base = 𝟙 X.base := rfl

/-- The fiber component of an identity is the normality transport. -/
@[simp] theorem id_fiber (X : F.Grothendieck) :
    (𝟙 X : X ⟶ X).fiber = eqToHom (by
      change X.fiber = (F.map (𝟙 X.base)).obj X.fiber
      rw [F.map_id]; rfl) := rfl

/-- Composition projects to composition in the base. -/
@[simp] theorem comp_base {X Y Z : F.Grothendieck} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

/-- The explicit fiber formula for composition in the total category. -/
@[simp] theorem comp_fiber {X Y Z : F.Grothendieck} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫ (F.map f.base).map g.fiber ≫ (F.mapComp f.base g.base).app Z.fiber := rfl

/-- The projection from the total category to its base. -/
def projection : F.Grothendieck ⥤ I where
  obj X := X.base
  map f := f.base

end Grothendieck
/-! ## Split indexed categories -/

/-- An ordinary contravariant functor gives normal lax data whose comparisons are
only equality transformations. Thus its total category uses the same construction. -/
def ofFunctor (F : Iᵒᵖ ⥤ Cat.{v₁, u₁}) : NormalLaxIndexedCategory I where
  fiber i := F.obj (op i)
  map f := (F.map f.op).toFunctor
  map_id i := by rw [op_id, F.map_id]; rfl
  mapComp f g := eqToHom (by rw [op_comp, F.map_comp]; rfl)
  mapComp_id_left f := rfl
  mapComp_id_right f := rfl
  mapComp_assoc f g h x := by simp [eqToHom_app, eqToHom_map]

/-- The split composition comparison is exactly the transport supplied by functoriality. -/
@[simp] theorem ofFunctor_mapComp (F : Iᵒᵖ ⥤ Cat.{v₁, u₁}) {i j k : I}
    (f : i ⟶ j) (g : j ⟶ k) :
    ((ofFunctor F).mapComp f g) = eqToHom (by
      change (F.map g.op).toFunctor ⋙ (F.map f.op).toFunctor =
        (F.map (f ≫ g).op).toFunctor
      rw [op_comp, F.map_comp]; rfl) := rfl

/-- Strictly compositional reindexing data assemble into an ordinary contravariant
functor. To recover the lax comparisons as well, require them to be equality transformations. -/
def toFunctor (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I)
    (hc : ∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), F.map g ⋙ F.map f = F.map (f ≫ g)) :
    Iᵒᵖ ⥤ Cat.{v₁, u₁} where
  obj i := F.fiber i.unop
  map f := (F.map f.unop).toCatHom
  map_id i := by dsimp; rw [F.map_id]; rfl
  map_comp f g := by
    dsimp
    rw [← hc g.unop f.unop]
    rfl

/-- When every comparison is the equality transformation for strict composition,
conversion to an ordinary functor and back recovers all the normal lax data. -/
theorem ofFunctor_toFunctor (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I)
    (hc : ∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), F.map g ⋙ F.map f = F.map (f ≫ g))
    (hκ : ∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), F.mapComp f g = eqToHom (hc f g)) :
    ofFunctor (F.toFunctor hc) = F := by
  cases F with
  | mk fiber map map_id mapComp mapComp_id_left mapComp_id_right mapComp_assoc =>
    dsimp [ofFunctor, toFunctor]
    congr
    funext i j k f g
    exact (hκ f g).symm

end NormalLaxIndexedCategory

namespace NormalLaxIndexedCategory

variable {I}

/-- Strict normal data give invertible-unit lax data by equality isomorphisms. -/
def toLax (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I) : LaxIndexedCategory I where
  fiber := F.fiber
  map := F.map
  mapId i := eqToIso (F.map_id i).symm
  mapComp := F.mapComp
  mapComp_id_left f x := by simp [F.mapComp_id_left, eqToHom_app]
  mapComp_id_right f x := by simp [F.mapComp_id_right, eqToHom_app, eqToHom_map]
  mapComp_assoc := F.mapComp_assoc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Embed the strict-normal total construction in the invertible-unit construction.
Both components of every object and arrow are retained. -/
def toLaxTotal (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I) :
    F.Grothendieck ⥤ F.toLax.Grothendieck where
  obj X := ⟨X.base, X.fiber⟩
  map f := ⟨f.base, f.fiber⟩
  map_id X := by
    refine LaxIndexedCategory.Grothendieck.Hom.ext (F := F.toLax) _ _ ?_ ?_
    · rfl
    · simp [LaxIndexedCategory.Grothendieck.id_fiber, Grothendieck.id_fiber,
      toLax, eqToHom_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Recover the strict-normal total construction from its invertible-unit version. -/
def fromLaxTotal (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I) :
    F.toLax.Grothendieck ⥤ F.Grothendieck where
  obj X := ⟨X.base, X.fiber⟩
  map f := ⟨f.base, f.fiber⟩
  map_id X := by
    refine Grothendieck.Hom.ext (F := F) _ _ ?_ ?_
    · rfl
    · simp [LaxIndexedCategory.Grothendieck.id_fiber, Grothendieck.id_fiber,
      toLax, eqToHom_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Strict normal data have equivalent total categories under the generalized
construction, with identity maps on all base and fiber components. -/
def totalEquivalence (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I) :
    F.Grothendieck ≌ F.toLax.Grothendieck where
  functor := F.toLaxTotal
  inverse := F.fromLaxTotal
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by simp

/-- The embedding of strict-normal total categories preserves projection strictly. -/
@[simp] theorem toLaxTotal_comp_projection (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I) :
    F.toLaxTotal ⋙ LaxIndexedCategory.Grothendieck.projection =
      Grothendieck.projection := rfl

/-- The inverse embedding also preserves projection strictly. -/
@[simp] theorem fromLaxTotal_comp_projection (F : NormalLaxIndexedCategory.{u, v, u₁, v₁} I) :
    F.fromLaxTotal ⋙ Grothendieck.projection =
      LaxIndexedCategory.Grothendieck.projection := rfl

end NormalLaxIndexedCategory

namespace LaxIndexedCategory

variable {I}

/-- An ordinary contravariant functor is a special case with equality comparisons
and equality unit isomorphisms. -/
def ofFunctor (F : Iᵒᵖ ⥤ Cat.{v₁, u₁}) : LaxIndexedCategory I :=
  (NormalLaxIndexedCategory.ofFunctor F).toLax

end LaxIndexedCategory

namespace SplitIndexedCategory

variable {I}

/-- The total category of a split indexed category, as the special case of the lax construction. -/
abbrev Grothendieck (F : Iᵒᵖ ⥤ Cat.{v₁, u₁}) :=
  (NormalLaxIndexedCategory.ofFunctor F).Grothendieck

/-- Projection from the split total category to the base. -/
abbrev projection (F : Iᵒᵖ ⥤ Cat.{v₁, u₁}) : Grothendieck F ⥤ I :=
  NormalLaxIndexedCategory.Grothendieck.projection

/-- Naturality of a transformation of split indexed categories, as equality of
reindexing functors followed by its fiber functors. -/
theorem reindexing_naturality {F G : Iᵒᵖ ⥤ Cat.{v₁, u₁}} (α : F ⟶ G)
    {i j : I} (f : i ⟶ j) :
    (F.map f.op).toFunctor ⋙ (α.app (op i)).toFunctor =
      (α.app (op j)).toFunctor ⋙ (G.map f.op).toFunctor :=
  congrArg Cat.Hom.toFunctor (α.naturality f.op)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation induces a functor between total categories.
On a fiber arrow it applies the component functor, then transports along naturality. -/
def map {F G : Iᵒᵖ ⥤ Cat.{v₁, u₁}} (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G where
  obj X := ⟨X.base, (α.app (op X.base)).toFunctor.obj X.fiber⟩
  map {X Y} f := ⟨f.base, (α.app (op X.base)).toFunctor.map f.fiber ≫
    eqToHom (Functor.congr_obj (reindexing_naturality α f.base) Y.fiber)⟩
  map_id X := by
    refine NormalLaxIndexedCategory.Grothendieck.Hom.ext _ _ (by rfl) ?_
    simp [NormalLaxIndexedCategory.Grothendieck.id_fiber, eqToHom_map]
  map_comp {X Y Z} f g := by
    refine NormalLaxIndexedCategory.Grothendieck.Hom.ext _ _ (by rfl) ?_
    simp only [NormalLaxIndexedCategory.Grothendieck.comp_fiber,
      NormalLaxIndexedCategory.ofFunctor, Functor.map_comp, eqToHom_app,
      eqToHom_map, Category.assoc]
    have hn := (eqToHom (reindexing_naturality α f.base)).naturality g.fiber
    simp only [eqToHom_app, Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp

/-- The induced total functor commutes strictly with the projections. -/
@[simp] theorem map_comp_projection {F G : Iᵒᵖ ⥤ Cat.{v₁, u₁}} (α : F ⟶ G) :
    map α ⋙ projection G = projection F := rfl

/-- A transformation of split indexed categories also acts on their total
categories formed with invertible units. This agrees with the strict construction
under the canonical equivalences. -/
def laxMap {F G : Iᵒᵖ ⥤ Cat.{v₁, u₁}} (α : F ⟶ G) :
    (LaxIndexedCategory.ofFunctor F).Grothendieck ⥤
      (LaxIndexedCategory.ofFunctor G).Grothendieck :=
  (NormalLaxIndexedCategory.ofFunctor F).fromLaxTotal ⋙ map α ⋙
    (NormalLaxIndexedCategory.ofFunctor G).toLaxTotal

/-- The induced functor on generalized split total categories preserves projection. -/
@[simp] theorem laxMap_comp_projection {F G : Iᵒᵖ ⥤ Cat.{v₁, u₁}} (α : F ⟶ G) :
    laxMap α ⋙ LaxIndexedCategory.Grothendieck.projection =
      LaxIndexedCategory.Grothendieck.projection := rfl

end SplitIndexedCategory
end CategorialAlgebras
