import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Whiskering

/-!
# Coherent projective systems of categories

Transition functors compose up to specified natural isomorphisms. Compatible
objects and morphisms form a category, so its universal property includes both
functors and natural transformations. No strict equality of transition functors
is required.
-/

universe u v w x

namespace CategorialAlgebras.Limits

open CategoryTheory

variable (C : ℕ → Type u) [∀ n, Category.{v} (C n)]

/-- A projective system with canonical composition and identity identifications. -/
structure ProjectiveSystem where
  /-- Restriction from level $n$ to level $m$. -/
  truncation : ∀ {m n}, m ≤ n → C n ⥤ C m
  /-- Restriction within one level is identity. -/
  identity : ∀ n, truncation (le_refl n) ≅ 𝟭 (C n)
  /-- Successive restrictions agree with direct restriction. -/
  composition : ∀ {m n p} (h : m ≤ n) (k : n ≤ p),
    truncation k ⋙ truncation h ≅ truncation (le_trans h k)
  /-- The two identifications of three successive restrictions coincide. -/
  associativity : ∀ {l m n p} (h : l ≤ m) (k : m ≤ n) (q : n ≤ p) (A : C p),
    (truncation h).map ((composition k q).hom.app A) ≫
        (composition h (le_trans k q)).hom.app A =
      (composition h k).hom.app ((truncation q).obj A) ≫
        (composition (le_trans h k) q).hom.app A
  /-- Removing an identity restriction at the lower end. -/
  identity_lower : ∀ {m n} (h : m ≤ n) (A : C n),
    (composition (le_refl m) h).hom.app A =
      (identity m).hom.app ((truncation h).obj A)
  /-- Removing an identity restriction at the upper end. -/
  identity_upper : ∀ {m n} (h : m ≤ n) (A : C n),
    (composition h (le_refl n)).hom.app A =
      (truncation h).map ((identity n).hom.app A)

variable {C}

namespace ProjectiveSystem

variable (T : ProjectiveSystem C)

/-- An object at every finite level, with coherent isomorphisms identifying its restrictions. -/
structure Family where
  /-- The finite-level objects. -/
  obj : ∀ n, C n
  /-- Identifications of the restrictions with the lower-level objects. -/
  transition : ∀ {m n} (h : m ≤ n), (T.truncation h).obj (obj n) ≅ obj m
  /-- The identification at a single level is the canonical one. -/
  identity : ∀ n, (transition (le_refl n)).hom = (T.identity n).hom.app (obj n)
  /-- The identifications respect composition of restrictions. -/
  coherence : ∀ {m n p} (h : m ≤ n) (k : n ≤ p),
    (T.truncation h).map (transition k).hom ≫ (transition h).hom =
      (T.composition h k).hom.app (obj p) ≫ (transition (le_trans h k)).hom

namespace Family

/-- A family of morphisms commuting with the restriction identifications. -/
@[ext] structure Hom (A B : T.Family) where
  /-- The morphism at each finite level. -/
  app : ∀ n, A.obj n ⟶ B.obj n
  /-- Commutativity after every restriction. -/
  comm : ∀ {m n} (h : m ≤ n),
    (T.truncation h).map (app n) ≫ (B.transition h).hom =
      (A.transition h).hom ≫ app m

/-- The identity family of morphisms. -/
def Hom.id (A : T.Family) : Hom T A A where
  app n := 𝟙 (A.obj n)
  comm h := by simp

/-- Composition of compatible morphisms is levelwise composition. -/
def Hom.comp {A B D : T.Family} (f : Hom T A B) (g : Hom T B D) : Hom T A D where
  app n := f.app n ≫ g.app n
  comm h := by rw [Functor.map_comp, Category.assoc, g.comm,
    ← Category.assoc, f.comm, Category.assoc]

/-- Compatible objects and compatible morphisms form a category. -/
instance : Category T.Family where
  Hom := Hom T
  id := Hom.id T
  comp := Hom.comp T
  id_comp f := by ext n; exact Category.id_comp _
  comp_id f := by ext n; exact Category.comp_id _
  assoc f g h := by ext n; exact Category.assoc _ _ _

/-- Evaluation of a compatible family at one finite level. -/
def evaluation (n : ℕ) : T.Family ⥤ C n where
  obj A := A.obj n
  map f := f.app n

/-- Compatible levelwise isomorphisms give an isomorphism of families. -/
def isoMk {A B : T.Family} (e : ∀ n, A.obj n ≅ B.obj n)
    (he : ∀ {m n} (h : m ≤ n),
      (T.truncation h).map (e n).hom ≫ (B.transition h).hom =
        (A.transition h).hom ≫ (e m).hom) : A ≅ B where
  hom := ⟨fun n => (e n).hom, he⟩
  inv := ⟨fun n => (e n).inv, fun {m n} h => by
    apply (cancel_mono (e m).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← he, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.id_comp]⟩
  hom_inv_id := by apply Hom.ext; funext n; exact (e n).hom_inv_id
  inv_hom_id := by apply Hom.ext; funext n; exact (e n).inv_hom_id

end Family

/-- A family of functors whose restriction identifications are natural and coherent. -/
structure FunctorFamily (L : Type w) [Category.{x} L] where
  /-- The functor at level $n$. -/
  functor : ∀ n, L ⥤ C n
  /-- Natural identifications between successive levels. -/
  transition : ∀ {m n} (h : m ≤ n), functor n ⋙ T.truncation h ≅ functor m
  /-- The identity identification is canonical. -/
  identity : ∀ n (X : L),
    (transition (le_refl n)).hom.app X = (T.identity n).hom.app ((functor n).obj X)
  /-- Naturality data satisfy the composition coherence. -/
  coherence : ∀ {m n p} (h : m ≤ n) (k : n ≤ p) (X : L),
    (T.truncation h).map ((transition k).hom.app X) ≫ (transition h).hom.app X =
      (T.composition h k).hom.app ((functor p).obj X) ≫
        (transition (le_trans h k)).hom.app X

/-- Assemble a coherent family of functors into a functor to compatible families. -/
def FunctorFamily.toFunctor {L : Type w} [Category.{x} L] (F : T.FunctorFamily L) :
    L ⥤ T.Family where
  obj X :=
    { obj n := (F.functor n).obj X
      transition h := (F.transition h).app X
      identity n := F.identity n X
      coherence h k := F.coherence h k X }
  map f :=
    { app n := (F.functor n).map f
      comm h := (F.transition h).hom.naturality f }
  map_id X := by apply Family.Hom.ext; funext n; exact (F.functor n).map_id X
  map_comp f g := by apply Family.Hom.ext; funext n; exact (F.functor n).map_comp f g

/-- A functor to compatible families determines its coherent finite-level functors. -/
def functorFamily {L : Type w} [Category.{x} L] (F : L ⥤ T.Family) : T.FunctorFamily L where
  functor n := F ⋙ Family.evaluation T n
  transition h := NatIso.ofComponents (fun X => ((F.obj X).transition h)) (fun f =>
    (F.map f).comm h)
  identity n X := (F.obj X).identity n
  coherence h k X := (F.obj X).coherence h k

end ProjectiveSystem

end CategorialAlgebras.Limits
