import CategorialAlgebras.Preliminaries.Algebra
import Mathlib.Data.Part
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Partial algebras

Partial operations take word-indexed families to `Part`. Homomorphisms preserve defined
values. Total algebras embed fully faithfully, isomorphisms are bijective homomorphisms
reflecting definedness, and products have componentwise domains and values.
-/

universe u v w w' w'' i

namespace CategorialAlgebras

/-! ## Families of partial values -/

/-- Assemble a dependent family of partial values, defined exactly when every entry is. -/
def partFamily {I : Type i} {A : I → Type w} (p : ∀ j, Part (A j)) : Part (∀ j, A j) where
  Dom := ∀ j, (p j).Dom
  get h j := (p j).get (h j)

/-- Membership in an assembled family is componentwise membership. -/
theorem mem_partFamily {I : Type i} {A : I → Type w} (p : ∀ j, Part (A j))
    (x : ∀ j, A j) : x ∈ partFamily p ↔ ∀ j, x j ∈ p j := by
  constructor
  · rintro ⟨h, rfl⟩ j
    exact Part.get_mem (h j)
  · intro h
    refine ⟨fun j => (h j).1, ?_⟩
    funext j
    exact (h j).2

/-- A partial algebra structure on a fixed sorted carrier. -/
abbrev PartialAlgebraStructure {S : Type u} (sig : Signature.{u, v} S)
    (A : S → Type w) := ∀ {a s}, sig a s → Word.Family A a → Part (A s)

/-- A many-sorted partial algebra. -/
structure PartialAlgebra {S : Type u} (sig : Signature.{u, v} S) where
  /-- The sorted carrier. -/
  carrier : S → Type w
  /-- The partial interpretation of every operation symbol. -/
  op : PartialAlgebraStructure sig carrier

namespace PartialAlgebra

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} {sig : Signature.{u, v} S}

/-! ## Homomorphisms -/

/-- A homomorphism preserves each defined operation value. -/
@[ext] structure Hom (A : PartialAlgebra.{u, v, w} sig)
    (B : PartialAlgebra.{u, v, w'} sig) where
  /-- The underlying total sorted mapping. -/
  toMap : SortedSet.Map A.carrier B.carrier
  /-- Preservation of defined values, hence also of definedness. -/
  map_op : ∀ {a s} (σ : sig a s) (x : Word.Family A.carrier a) {y},
    y ∈ A.op σ x → toMap s y ∈ B.op σ (fun j => toMap _ (x j))

/-- Identity homomorphism. -/
def Hom.id (A : PartialAlgebra.{u, v, w} sig) : Hom A A where
  toMap _ := _root_.id
  map_op _ _ _ h := h

/-- Composition in diagrammatic order. -/
def Hom.comp {A : PartialAlgebra.{u, v, w} sig} {B : PartialAlgebra.{u, v, w'} sig}
    {C : PartialAlgebra.{u, v, w''} sig} (f : Hom A B) (g : Hom B C) : Hom A C where
  toMap s x := g.toMap s (f.toMap s x)
  map_op σ x _ h := g.map_op σ _ (f.map_op σ x h)

/-- Partial algebras with carriers in a fixed universe form a category. -/
instance : Category (PartialAlgebra.{u, v, w} sig) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The forgetful functor to sorted sets. -/
def forget (sig : Signature.{u, v} S) :
    PartialAlgebra.{u, v, w} sig ⥤ SortedSet.{u, w} S where
  obj A := A.carrier
  map f := SortedSet.homOfMap f.toMap

/-- A homomorphism preserves definedness. -/
theorem Hom.map_dom {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, w'} sig} (f : Hom A B) {a s} (σ : sig a s)
    (x : Word.Family A.carrier a) (h : (A.op σ x).Dom) :
    (B.op σ (fun j => f.toMap _ (x j))).Dom :=
  (f.map_op σ x (Part.get_mem h)).1

/-! ## Total algebras -/

/-- Regard a total algebra as a partial algebra with everywhere defined operations. -/
abbrev ofAlgebra (A : Algebra.{u, v, w} sig) : PartialAlgebra sig where
  carrier := A.carrier
  op σ x := Part.some (A.op σ x)

/-- Inclusion of total algebras into partial algebras. -/
def totalInclusion (sig : Signature.{u, v} S) :
    Algebra.{u, v, w} sig ⥤ PartialAlgebra.{u, v, w} sig where
  obj := ofAlgebra
  map f :=
    { toMap := f.toMap
      map_op := fun σ x _ h => by
        rw [Part.mem_some_iff] at h ⊢
        rw [h, f.map_op] }

/-- The inclusion of total algebras is fully faithful. -/
def totalInclusionFullyFaithful (sig : Signature.{u, v} S) :
    (totalInclusion.{u, v, w} sig).FullyFaithful where
  preimage f :=
    { toMap := f.toMap
      map_op := fun σ x => (Part.mem_some_iff.mp (f.map_op σ x (Part.mem_some _))) }
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- The total inclusion is full. -/
instance totalInclusion_full : (totalInclusion.{u, v, w} sig).Full :=
  (totalInclusionFullyFaithful sig).full

/-- The total inclusion is faithful. -/
instance totalInclusion_faithful : (totalInclusion.{u, v, w} sig).Faithful :=
  (totalInclusionFullyFaithful sig).faithful

/-! ## Isomorphisms -/

/-- Reflection of the domains of all basic operations. -/
def Hom.ReflectsDefinedness {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, w'} sig} (f : Hom A B) : Prop :=
  ∀ {a s} (σ : sig a s) (x : Word.Family A.carrier a),
    (B.op σ (fun j => f.toMap _ (x j))).Dom → (A.op σ x).Dom

/-- A bijective homomorphism reflecting definedness has a homomorphic inverse. -/
noncomputable def Hom.inverse {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, w'} sig} (f : Hom A B)
    (hb : ∀ s, Function.Bijective (f.toMap s)) (hr : f.ReflectsDefinedness) : Hom B A where
  toMap s := (Equiv.ofBijective (f.toMap s) (hb s)).symm
  map_op := by
    intro a s σ x y hy
    let e s := Equiv.ofBijective (f.toMap s) (hb s)
    have hx : (fun j => f.toMap _ ((e _).symm (x j))) = x := by
      funext j
      exact (e _).apply_symm_apply _
    have hd := hr σ (fun j => (e _).symm (x j)) (by rw [hx]; exact hy.1)
    have hm := f.map_op σ _ (Part.get_mem hd)
    rw [hx] at hm
    have he := Part.mem_unique hm hy
    have hv : (e s).symm y = (A.op σ (fun j => (e _).symm (x j))).get hd := by
      apply (e s).injective
      rw [Equiv.apply_symm_apply]
      exact he.symm
    rw [hv]
    exact Part.get_mem hd

/-- An isomorphism has a bijective underlying sorted mapping. -/
theorem Hom.bijective_of_isIso {A B : PartialAlgebra.{u, v, w} sig} (f : A ⟶ B)
    [IsIso f] : ∀ s, Function.Bijective (f.toMap s) := by
  intro s
  have hl (x : A.carrier s) : (inv f).toMap s (f.toMap s x) = x :=
    congrArg (fun h : A ⟶ A => h.toMap s x) (IsIso.hom_inv_id f)
  have hr (y : B.carrier s) : f.toMap s ((inv f).toMap s y) = y :=
    congrArg (fun h : B ⟶ B => h.toMap s y) (IsIso.inv_hom_id f)
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

/-- Isomorphisms reflect definedness. -/
theorem Hom.reflectsDefinedness_of_isIso {A B : PartialAlgebra.{u, v, w} sig}
    (f : A ⟶ B) [IsIso f] : f.ReflectsDefinedness := by
  intro a s σ x h
  have hd := (inv f).map_dom σ _ h
  have hx : (fun j => (inv f).toMap _ (f.toMap _ (x j))) = x := by
    funext j
    exact congrArg (fun k : A ⟶ A => k.toMap _ (x j)) (IsIso.hom_inv_id f)
  rwa [hx] at hd

/-- A homomorphism is invertible exactly when it is bijective and reflects definedness. -/
theorem Hom.isIso_iff_bijective_reflects {A B : PartialAlgebra.{u, v, w} sig}
    (f : A ⟶ B) : IsIso f ↔ (∀ s, Function.Bijective (f.toMap s)) ∧
      f.ReflectsDefinedness := by
  constructor
  · intro h
    exact ⟨f.bijective_of_isIso, f.reflectsDefinedness_of_isIso⟩
  · rintro ⟨hb, hr⟩
    refine ⟨f.inverse hb hr, ?_, ?_⟩
    · apply Hom.ext
      funext s x
      exact (Equiv.ofBijective (f.toMap s) (hb s)).symm_apply_apply x
    · apply Hom.ext
      funext s x
      exact (Equiv.ofBijective (f.toMap s) (hb s)).apply_symm_apply x

/-- A bijective homomorphism is invertible exactly when it reflects definedness. -/
theorem Hom.isIso_iff_reflects {A B : PartialAlgebra.{u, v, w} sig} (f : A ⟶ B)
    (hb : ∀ s, Function.Bijective (f.toMap s)) :
    IsIso f ↔ f.ReflectsDefinedness := by
  rw [f.isIso_iff_bijective_reflects]
  exact and_iff_right hb

/-- Invertibility is equivalent to bijectivity and a homomorphic inverse mapping.
For a bijective map its right inverse is necessarily its unique inverse. -/
theorem Hom.isIso_iff_inverse {A B : PartialAlgebra.{u, v, w} sig} (f : A ⟶ B) :
    IsIso f ↔ (∀ s, Function.Bijective (f.toMap s)) ∧
      ∃ g : B ⟶ A, ∀ s y, f.toMap s (g.toMap s y) = y := by
  constructor
  · intro h
    exact ⟨f.bijective_of_isIso, inv f, fun s y =>
      congrArg (fun k : B ⟶ B => k.toMap s y) (IsIso.inv_hom_id f)⟩
  · rintro ⟨hb, g, hg⟩
    refine ⟨g, ?_, ?_⟩
    · apply Hom.ext
      funext s x
      exact (hb s).injective (hg s (f.toMap s x))
    · apply Hom.ext
      exact funext fun s => funext (hg s)

/-! ## Products -/

/-- Product algebra; its operations are defined in every component simultaneously. -/
def product {I : Type i} (A : I → PartialAlgebra.{u, v, w} sig) : PartialAlgebra sig where
  carrier s := ∀ i, (A i).carrier s
  op σ x := partFamily (fun i => (A i).op σ (fun j => x j i))

/-- A product operation is defined exactly when all component operations are. -/
theorem product_op_dom {I : Type i} (A : I → PartialAlgebra.{u, v, w} sig)
    {a s} (σ : sig a s) (x : Word.Family (product A).carrier a) :
    ((product A).op σ x).Dom ↔ ∀ i, ((A i).op σ (fun j => x j i)).Dom := Iff.rfl

/-- The canonical projection from a product. -/
def projection {I : Type i} (A : I → PartialAlgebra.{u, v, w} sig) (i : I) :
    Hom (product A) (A i) where
  toMap _ x := x i
  map_op _ _ _ h := (mem_partFamily _ _).mp h i

/-- The homomorphism induced by a family of homomorphisms into the factors. -/
def productLift {I : Type i} {A : I → PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, w'} sig} (f : ∀ i, Hom B (A i)) : Hom B (product A) where
  toMap s x i := (f i).toMap s x
  map_op σ x _ h := (mem_partFamily _ _).mpr (fun i => (f i).map_op σ x h)

/-- The fan of canonical projections, with product index and carriers in a fixed universe. -/
def productFan {I : Type w} (A : I → PartialAlgebra.{u, v, w} sig) : Fan A :=
  Fan.mk (product A) (projection A)

/-- The componentwise product satisfies the categorical product universal property. -/
def productIsLimit {I : Type w} (A : I → PartialAlgebra.{u, v, w} sig) :
    IsLimit (productFan A) :=
  Fan.IsLimit.mk _ (fun c => productLift c.proj) (fun _ _ => rfl) (by
    intro c m hm
    apply Hom.ext
    funext s x i
    exact congrArg (fun f : c.pt ⟶ A i => f.toMap s x) (hm i))

end PartialAlgebra
end CategorialAlgebras
