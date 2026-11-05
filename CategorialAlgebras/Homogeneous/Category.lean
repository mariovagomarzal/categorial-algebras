import CategorialAlgebras.Preliminaries.PartialAlgebra
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Order.Hom.Basic

/-!
# Homogeneous higher categories

All cells inhabit one carrier. Each dimension has total source and target maps and a
partial composition; ordered pairs of dimensions satisfy globularity and interchange.
Composition is written with the later arrow first. Finite dimensions use `Fin n`.
-/

universe i i' u v

namespace CategorialAlgebras
namespace Homogeneous

open CategoryTheory

/-- A category structure on a single set of cells, including its identity arrows. -/
structure CategoryStructure (A : Type u) where
  /-- Source, represented by an identity cell. -/
  source : A → A
  /-- Target, represented by an identity cell. -/
  target : A → A
  /-- Partial composition, with the later arrow first. -/
  comp : A → A → Part A
  /-- Sources are identities. -/
  source_source : ∀ x, source (source x) = source x
  /-- Targets are fixed by source. -/
  source_target : ∀ x, source (target x) = target x
  /-- Sources are fixed by target. -/
  target_source : ∀ x, target (source x) = source x
  /-- Targets are identities. -/
  target_target : ∀ x, target (target x) = target x
  /-- Composition is defined exactly at matching boundaries. -/
  comp_dom : ∀ x y, (comp x y).Dom ↔ source x = target y
  /-- The source of a composite is the source of its earlier arrow. -/
  source_comp : ∀ x y z, z ∈ comp x y → source z = source y
  /-- The target of a composite is the target of its later arrow. -/
  target_comp : ∀ x y z, z ∈ comp x y → target z = target x
  /-- The source acts as a right unit. -/
  comp_source : ∀ x, x ∈ comp x (source x)
  /-- The target acts as a left unit. -/
  target_comp_self : ∀ x, x ∈ comp (target x) x
  /-- Two adjacent composites extend to equal triple composites. -/
  assoc : ∀ x y z xy yz, xy ∈ comp x y → yz ∈ comp y z →
    ∃ q, q ∈ comp xy z ∧ q ∈ comp x yz

/-- Compatibility of two category structures, the first in the lower dimension. -/
structure Compatible {A : Type u} (l k : CategoryStructure A) : Prop where
  /-- Higher source fixes lower sources. -/
  source_source : ∀ x, k.source (l.source x) = l.source x
  /-- Higher target fixes lower targets. -/
  target_target : ∀ x, k.target (l.target x) = l.target x
  /-- Lower source absorbs higher source. -/
  source_source_low : ∀ x, l.source (k.source x) = l.source x
  /-- Lower target absorbs higher target. -/
  target_target_low : ∀ x, l.target (k.target x) = l.target x
  /-- Lower source absorbs higher target. -/
  source_target : ∀ x, l.source (k.target x) = l.source x
  /-- Lower target absorbs higher source. -/
  target_source : ∀ x, l.target (k.source x) = l.target x
  /-- Higher source preserves lower composition. -/
  source_comp : ∀ x y z, z ∈ l.comp x y →
    k.source z ∈ l.comp (k.source x) (k.source y)
  /-- Higher target preserves lower composition. -/
  target_comp : ∀ x y z, z ∈ l.comp x y →
    k.target z ∈ l.comp (k.target x) (k.target y)
  /-- A composable rectangle has equal composites in either order. -/
  interchange : ∀ x y z t xy zt xz yt,
    xy ∈ l.comp x y → zt ∈ l.comp z t → xz ∈ k.comp x z → yt ∈ k.comp y t →
    ∃ q, q ∈ k.comp xy zt ∧ q ∈ l.comp xz yt

/-- Higher category structure indexed by an ordered type of dimensions. -/
structure Structure (I : Type i) [LT I] (A : Type u) where
  /-- A category structure in each dimension. -/
  dim : I → CategoryStructure A
  /-- Every increasing pair of dimensions is compatible. -/
  compatible : ∀ l k, l < k → Compatible (dim l) (dim k)

/-- A homogeneous higher category with bundled carrier. -/
structure HigherCategory (I : Type i) [LT I] where
  /-- The set of all cells. -/
  carrier : Type u
  /-- The dimension-indexed category structure. -/
  str : Structure I carrier

variable {I : Type i} [LT I]

/-- A cell of dimension at most $k$ is fixed by the $k$-source. -/
def Structure.IsCell {A : Type u} (C : Structure I A) (k : I) (x : A) : Prop :=
  (C.dim k).source x = x

/-- The subtype of cells fixed in a specified dimension. -/
def Structure.Cell {A : Type u} (C : Structure I A) (k : I) := {x : A // C.IsCell k x}

/-- Being fixed by source is equivalent to being fixed by target. -/
theorem Structure.isCell_iff_target {A : Type u} (C : Structure I A) (k : I) (x : A) :
    C.IsCell k x ↔ (C.dim k).target x = x := by
  constructor
  · intro h
    rw [← h, (C.dim k).target_source, h]
  · intro h
    change (C.dim k).source x = x
    rw [← h, (C.dim k).source_target, h]

/-- Cells remain cells in every higher dimension. -/
theorem Structure.isCell_mono {J : Type i'} [LinearOrder J] {A : Type u}
    (C : Structure J A) {j k : J} (h : j ≤ k) {x : A} (hx : C.IsCell j x) :
    C.IsCell k x := by
  rcases h.eq_or_lt with rfl | h
  · exact hx
  · change (C.dim k).source x = x
    rw [← hx, (C.compatible j k h).source_source, hx]

/-- A higher functor preserves boundaries and every defined composite. -/
@[ext] structure Functor (C : HigherCategory.{i, u} I) (D : HigherCategory.{i, v} I) where
  /-- The function on all cells. -/
  toFun : C.carrier → D.carrier
  /-- Preservation of sources in every dimension. -/
  map_source : ∀ k x, toFun ((C.str.dim k).source x) = (D.str.dim k).source (toFun x)
  /-- Preservation of targets in every dimension. -/
  map_target : ∀ k x, toFun ((C.str.dim k).target x) = (D.str.dim k).target (toFun x)
  /-- Preservation of defined composite values. -/
  map_comp : ∀ k x y z, z ∈ (C.str.dim k).comp x y →
    toFun z ∈ (D.str.dim k).comp (toFun x) (toFun y)

/-- The identity higher functor. -/
def Functor.id (C : HigherCategory.{i, u} I) : Functor C C where
  toFun := _root_.id
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ h := h

/-- Composition of higher functors in diagrammatic order. -/
def Functor.comp {C D E : HigherCategory.{i, u} I} (f : Functor C D) (g : Functor D E) :
    Functor C E where
  toFun := g.toFun ∘ f.toFun
  map_source k x := by simp only [Function.comp_apply, f.map_source, g.map_source]
  map_target k x := by simp only [Function.comp_apply, f.map_target, g.map_target]
  map_comp k x y z h := g.map_comp k _ _ _ (f.map_comp k x y z h)

/-- Higher categories and higher functors form a category. -/
instance : Category (HigherCategory.{i, u} I) where
  Hom := Functor
  id := Functor.id
  comp := Functor.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Higher functors preserve cells of every specified dimension. -/
theorem Functor.map_isCell {C D : HigherCategory.{i, u} I} (f : Functor C D)
    {k x} (h : C.str.IsCell k x) : D.str.IsCell k (f.toFun x) := by
  change (D.str.dim k).source (f.toFun x) = f.toFun x
  rw [← f.map_source, h]

/-- The map induced by a higher functor on the subtype of cells in a dimension. -/
def Functor.cellMap {C D : HigherCategory.{i, u} I} (f : Functor C D) (k : I) :
    C.str.Cell k → D.str.Cell k := fun x => ⟨f.toFun x.val, f.map_isCell x.property⟩

/-- Restrict a structure along an order embedding, without changing its carrier. -/
def Structure.restrict {J : Type i'} {K : Type i} [Preorder J] [Preorder K] {A : Type u}
    (C : Structure K A) (e : J ↪o K) : Structure J A where
  dim j := C.dim (e j)
  compatible _ _ h := C.compatible _ _ (e.lt_iff_lt.mpr h)

/-- Every cell is an identity in a discrete category structure. -/
def CategoryStructure.IsDiscrete {A : Type u} (C : CategoryStructure A) : Prop :=
  ∀ x, C.source x = x

/-- The discrete category structure on any type. -/
noncomputable def CategoryStructure.discrete (A : Type u) : CategoryStructure A where
  source := id
  target := id
  comp x y := ⟨x = y, fun _ => x⟩
  source_source _ := rfl
  source_target _ := rfl
  target_source _ := rfl
  target_target _ := rfl
  comp_dom _ _ := Iff.rfl
  source_comp _ _ _ h := h.2 ▸ h.1
  target_comp _ _ _ h := h.2.symm
  comp_source _ := ⟨rfl, rfl⟩
  target_comp_self _ := ⟨rfl, rfl⟩
  assoc x y z xy yz h h' := by
    rcases h with ⟨rfl, rfl⟩
    rcases h' with ⟨rfl, rfl⟩
    exact ⟨x, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The componentwise category structure on a dependent product of carriers. -/
def CategoryStructure.product {J : Type v} {A : J → Type u}
    (C : ∀ j, CategoryStructure (A j)) : CategoryStructure (∀ j, A j) where
  source x j := (C j).source (x j)
  target x j := (C j).target (x j)
  comp x y := partFamily (fun j => (C j).comp (x j) (y j))
  source_source x := funext (fun j => (C j).source_source (x j))
  source_target x := funext (fun j => (C j).source_target (x j))
  target_source x := funext (fun j => (C j).target_source (x j))
  target_target x := funext (fun j => (C j).target_target (x j))
  comp_dom x y := by simp only [partFamily, (C _).comp_dom, funext_iff]
  source_comp x y z h := funext (fun j => (C j).source_comp _ _ _
    ((mem_partFamily _ _).mp h j))
  target_comp x y z h := funext (fun j => (C j).target_comp _ _ _
    ((mem_partFamily _ _).mp h j))
  comp_source x := (mem_partFamily _ _).mpr (fun j => (C j).comp_source (x j))
  target_comp_self x := (mem_partFamily _ _).mpr (fun j => (C j).target_comp_self (x j))
  assoc x y z xy yz h h' := by
    classical
    have hj j := (C j).assoc _ _ _ _ _ ((mem_partFamily _ _).mp h j)
      ((mem_partFamily _ _).mp h' j)
    choose q hq hq' using hj
    exact ⟨q, (mem_partFamily _ _).mpr hq, (mem_partFamily _ _).mpr hq'⟩

/-- Products of compatible pairs are compatible componentwise. -/
theorem Compatible.product {J : Type v} {A : J → Type u}
    {l k : ∀ j, CategoryStructure (A j)} (h : ∀ j, Compatible (l j) (k j)) :
    Compatible (CategoryStructure.product l) (CategoryStructure.product k) where
  source_source x := funext (fun j => (h j).source_source (x j))
  target_target x := funext (fun j => (h j).target_target (x j))
  source_source_low x := funext (fun j => (h j).source_source_low (x j))
  target_target_low x := funext (fun j => (h j).target_target_low (x j))
  source_target x := funext (fun j => (h j).source_target (x j))
  target_source x := funext (fun j => (h j).target_source (x j))
  source_comp x y z hz := (mem_partFamily _ _).mpr
    (fun j => (h j).source_comp _ _ _ ((mem_partFamily _ _).mp hz j))
  target_comp x y z hz := (mem_partFamily _ _).mpr
    (fun j => (h j).target_comp _ _ _ ((mem_partFamily _ _).mp hz j))
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    classical
    have hj j := (h j).interchange _ _ _ _ _ _ _ _
      ((mem_partFamily _ _).mp hxy j) ((mem_partFamily _ _).mp hzt j)
      ((mem_partFamily _ _).mp hxz j) ((mem_partFamily _ _).mp hyt j)
    choose q hq hq' using hj
    exact ⟨q, (mem_partFamily _ _).mpr hq, (mem_partFamily _ _).mpr hq'⟩

/-- The componentwise higher category on a dependent product, including an empty product. -/
def HigherCategory.product {J : Type v} (C : J → HigherCategory.{i, u} I) :
    HigherCategory I where
  carrier := ∀ j, (C j).carrier
  str.dim k := CategoryStructure.product (fun j => (C j).str.dim k)
  str.compatible l k h := Compatible.product (fun j => (C j).str.compatible l k h)

/-- Projection from a componentwise higher category product. -/
def HigherCategory.projection {J : Type v} (C : J → HigherCategory.{i, u} I) (j : J) :
    Functor (HigherCategory.product C) (C j) where
  toFun x := x j
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ h := (mem_partFamily _ _).mp h j

/-- The higher functor induced by a family of higher functors into the factors. -/
def HigherCategory.productLift {J : Type v} {C : J → HigherCategory.{i, u} I}
    {D : HigherCategory.{i, u} I} (f : ∀ j, Functor D (C j)) :
    Functor D (HigherCategory.product C) where
  toFun x j := (f j).toFun x
  map_source k x := funext (fun j => (f j).map_source k x)
  map_target k x := funext (fun j => (f j).map_target k x)
  map_comp k x y z h := (mem_partFamily _ _).mpr (fun j => (f j).map_comp k x y z h)

/-- The fan of componentwise higher category projections. -/
def HigherCategory.productFan {J : Type u} (C : J → HigherCategory.{i, u} I) :
    Limits.Fan C := Limits.Fan.mk (HigherCategory.product C) (HigherCategory.projection C)

/-- The componentwise higher category product has the categorical product universal property. -/
def HigherCategory.productIsLimit {J : Type u} (C : J → HigherCategory.{i, u} I) :
    Limits.IsLimit (HigherCategory.productFan C) :=
  Limits.Fan.IsLimit.mk _ (fun c => HigherCategory.productLift c.proj) (fun _ _ => rfl) (by
    intro c m hm
    apply Functor.ext
    funext x j
    exact congrArg (fun f : c.pt ⟶ C j => f.toFun x) (hm j))

/-- Two copies of a discrete category structure are compatible. -/
theorem CategoryStructure.discrete_compatible (A : Type u) :
    Compatible (CategoryStructure.discrete A) (CategoryStructure.discrete A) where
  source_source _ := rfl
  target_target _ := rfl
  source_source_low _ := rfl
  target_target_low _ := rfl
  source_target _ := rfl
  target_source _ := rfl
  source_comp _ _ _ h := h
  target_comp _ _ _ h := h
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    rcases hxy with ⟨hxy, hxy'⟩
    rcases hzt with ⟨hzt, hzt'⟩
    rcases hxz with ⟨hxz, hxz'⟩
    rcases hyt with ⟨hyt, hyt'⟩
    change x = y at hxy
    change z = t at hzt
    change x = z at hxz
    subst y
    subst t
    subst z
    change x = xy at hxy'
    change x = zt at hzt'
    change x = xz at hxz'
    change x = yt at hyt'
    subst xy
    subst zt
    subst xz
    subst yt
    exact ⟨x, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The discrete higher category on a set, in any dimension type. -/
noncomputable def HigherCategory.discrete (I : Type i) [LT I] (A : Type u) :
    HigherCategory I where
  carrier := A
  str.dim _ := CategoryStructure.discrete A
  str.compatible _ _ _ := CategoryStructure.discrete_compatible A

/-- Every cell of a discrete higher category is fixed by every source. -/
theorem HigherCategory.discrete_isCell (A : Type u) (k : I) (x : A) :
    (HigherCategory.discrete I A).str.IsCell k x := rfl

/-- A homogeneous $n$-category has dimensions `Fin n`; in particular this covers $0,1,2$. -/
abbrev NCategory (n : ℕ) := HigherCategory (Fin n)

/-- Every cell has some finite dimension. -/
def HigherCategory.FiniteDimensional (C : HigherCategory ℕ) : Prop :=
  ∀ x : C.carrier, ∃ k, C.str.IsCell k x

/-- Homogeneous $\omega$-categories form the full subcategory of locally finite cells. -/
abbrev OmegaCategory := ObjectProperty.FullSubcategory
  (HigherCategory.FiniteDimensional : ObjectProperty (HigherCategory.{0, u} ℕ))

end Homogeneous
end CategorialAlgebras
