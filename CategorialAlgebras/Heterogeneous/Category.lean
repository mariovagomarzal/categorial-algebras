import CategorialAlgebras.Preliminaries.PartialAlgebra
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Fin.Basic

/-!
# Heterogeneous higher categories

Cells have separate carriers in each dimension. Each increasing pair of dimensions has
boundaries, identities and a partial composition with precisely the matching-boundary
domain. Increasing triples satisfy globularity, preservation and interchange.
-/

universe i i' u v

namespace CategorialAlgebras.Heterogeneous

open CategoryTheory

/-! ## Category structures and compatibility -/

/-- A category with an object carrier $A$ and an arrow carrier $B$. -/
structure CategoryStructure (A B : Type u) where
  /-- Source of an arrow. -/
  source : B → A
  /-- Target of an arrow. -/
  target : B → A
  /-- Identity arrow of an object. -/
  identity : A → B
  /-- Composition, with the later arrow first. -/
  comp : B → B → Part B
  /-- Source of an identity. -/
  source_identity : ∀ x, source (identity x) = x
  /-- Target of an identity. -/
  target_identity : ∀ x, target (identity x) = x
  /-- Composition is defined exactly on the fiber product of the boundaries. -/
  comp_dom : ∀ x y, (comp x y).Dom ↔ source x = target y
  /-- Source of a composite. -/
  source_comp : ∀ x y z, z ∈ comp x y → source z = source y
  /-- Target of a composite. -/
  target_comp : ∀ x y z, z ∈ comp x y → target z = target x
  /-- The identity of the source is a right unit. -/
  comp_source : ∀ x, x ∈ comp x (identity (source x))
  /-- The identity of the target is a left unit. -/
  target_comp_self : ∀ x, x ∈ comp (identity (target x)) x
  /-- Adjacent composites extend to equal triple composites. -/
  assoc : ∀ x y z xy yz, xy ∈ comp x y → yz ∈ comp y z →
    ∃ q, q ∈ comp xy z ∧ q ∈ comp x yz

/-- Choose source (`false`) or target (`true`). -/
def CategoryStructure.boundary {A B : Type u} (C : CategoryStructure A B) (b : Bool) :
    B → A := if b then C.target else C.source

/-- Compatibility of the three pairs in an increasing triple of dimensions. -/
structure Compatible {A B C : Type u} (l : CategoryStructure A B)
    (k : CategoryStructure B C) (m : CategoryStructure A C) : Prop where
  /-- Either higher boundary has the same lower boundaries. -/
  globular : ∀ b c x, l.boundary b (k.boundary c x) = m.boundary b x
  /-- Successive identities equal the direct identity. -/
  identity_identity : ∀ x, k.identity (l.identity x) = m.identity x
  /-- Higher boundaries preserve lower composition. -/
  boundary_comp : ∀ b x y z, z ∈ m.comp x y →
    k.boundary b z ∈ l.comp (k.boundary b x) (k.boundary b y)
  /-- Identities preserve lower composition. -/
  identity_comp : ∀ x y z, z ∈ l.comp x y →
    k.identity z ∈ m.comp (k.identity x) (k.identity y)
  /-- A composable rectangle has the same composite in either order. -/
  interchange : ∀ x y z t xy zt xz yt,
    xy ∈ k.comp x y → zt ∈ k.comp z t → xz ∈ m.comp x z → yt ∈ m.comp y t →
    ∃ q, q ∈ m.comp xy zt ∧ q ∈ k.comp xz yt

/-- Higher category structure on a dimension-indexed family of carriers. -/
structure Structure (I : Type i) [Preorder I] (A : I → Type u) where
  /-- Category structure for each increasing pair. -/
  dim : ∀ j k, j < k → CategoryStructure (A j) (A k)
  /-- Compatibility for each increasing triple. -/
  compatible : ∀ h j k (hj : h < j) (jk : j < k),
    Compatible (dim h j hj) (dim j k jk) (dim h k (lt_trans hj jk))

/-- A higher category with a separate carrier in every dimension. -/
structure HigherCategory (I : Type i) [Preorder I] where
  /-- Cells of each dimension. -/
  carrier : I → Type u
  /-- The categorical structure of these cells. -/
  str : Structure I carrier

variable {I : Type i} [Preorder I]

/-! ## Higher functors -/

/-- A higher functor preserves all boundaries, identities and defined composites. -/
@[ext] structure Functor (C : HigherCategory.{i, u} I) (D : HigherCategory.{i, v} I) where
  /-- The function on cells in each dimension. -/
  toFun : ∀ k, C.carrier k → D.carrier k
  /-- Preservation of sources. -/
  map_source : ∀ j k (h : j < k) x,
    toFun j ((C.str.dim j k h).source x) = (D.str.dim j k h).source (toFun k x)
  /-- Preservation of targets. -/
  map_target : ∀ j k (h : j < k) x,
    toFun j ((C.str.dim j k h).target x) = (D.str.dim j k h).target (toFun k x)
  /-- Preservation of identities. -/
  map_identity : ∀ j k (h : j < k) x,
    toFun k ((C.str.dim j k h).identity x) = (D.str.dim j k h).identity (toFun j x)
  /-- Preservation of defined composites. -/
  map_comp : ∀ j k (h : j < k) x y z, z ∈ (C.str.dim j k h).comp x y →
    toFun k z ∈ (D.str.dim j k h).comp (toFun k x) (toFun k y)

/-- The identity higher functor. -/
def Functor.id (C : HigherCategory.{i, u} I) : Functor C C where
  toFun _ := _root_.id
  map_source _ _ _ _ := rfl
  map_target _ _ _ _ := rfl
  map_identity _ _ _ _ := rfl
  map_comp _ _ _ _ _ _ h := h

/-- Composition of higher functors in diagrammatic order. -/
def Functor.comp {C D E : HigherCategory.{i, u} I} (f : Functor C D) (g : Functor D E) :
    Functor C E where
  toFun k := g.toFun k ∘ f.toFun k
  map_source j k h x := by simp only [Function.comp_apply, f.map_source, g.map_source]
  map_target j k h x := by simp only [Function.comp_apply, f.map_target, g.map_target]
  map_identity j k h x := by simp only [Function.comp_apply, f.map_identity, g.map_identity]
  map_comp j k h x y z hz := g.map_comp j k h _ _ _ (f.map_comp j k h x y z hz)

/-- Higher categories and higher functors form a category. -/
instance : Category (HigherCategory.{i, u} I) where
  Hom := Functor
  id := Functor.id
  comp := Functor.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ## Restriction and products -/

/-- Restriction of dimensions along an order embedding. -/
def Structure.restrict {J : Type i'} [Preorder J] {A : I → Type u}
    (C : Structure I A) (e : J ↪o I) : Structure J (fun j => A (e j)) where
  dim j k h := C.dim (e j) (e k) (e.lt_iff_lt.mpr h)
  compatible _ _ _ _ _ := C.compatible _ _ _ _ _

/-- The componentwise category structure on dependent products. -/
def CategoryStructure.product {J : Type v} {A B : J → Type u}
    (C : ∀ j, CategoryStructure (A j) (B j)) : CategoryStructure (∀ j, A j) (∀ j, B j) where
  source x j := (C j).source (x j)
  target x j := (C j).target (x j)
  identity x j := (C j).identity (x j)
  comp x y := partFamily (fun j => (C j).comp (x j) (y j))
  source_identity x := funext (fun j => (C j).source_identity (x j))
  target_identity x := funext (fun j => (C j).target_identity (x j))
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

/-- Boundaries of a product are computed pointwise. -/
@[simp] theorem CategoryStructure.product_boundary {J : Type v} {A B : J → Type u}
    (C : ∀ j, CategoryStructure (A j) (B j)) (b : Bool) (x : ∀ j, B j) :
    (CategoryStructure.product C).boundary b x = fun j => (C j).boundary b (x j) := by
  cases b <;> rfl

/-- Products preserve compatibility of increasing triples. -/
theorem Compatible.product {J : Type v} {A B C : J → Type u}
    {l : ∀ j, CategoryStructure (A j) (B j)} {k : ∀ j, CategoryStructure (B j) (C j)}
    {m : ∀ j, CategoryStructure (A j) (C j)} (h : ∀ j, Compatible (l j) (k j) (m j)) :
    Compatible (CategoryStructure.product l) (CategoryStructure.product k)
      (CategoryStructure.product m) where
  globular b c x := by simpa using funext (fun j => (h j).globular b c (x j))
  identity_identity x := funext (fun j => (h j).identity_identity (x j))
  boundary_comp b x y z hz := by
    simp only [CategoryStructure.product_boundary]
    exact (mem_partFamily _ _).mpr
      (fun j => (h j).boundary_comp b _ _ _ ((mem_partFamily _ _).mp hz j))
  identity_comp x y z hz := (mem_partFamily _ _).mpr
    (fun j => (h j).identity_comp _ _ _ ((mem_partFamily _ _).mp hz j))
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    classical
    have hj j := (h j).interchange _ _ _ _ _ _ _ _
      ((mem_partFamily _ _).mp hxy j) ((mem_partFamily _ _).mp hzt j)
      ((mem_partFamily _ _).mp hxz j) ((mem_partFamily _ _).mp hyt j)
    choose q hq hq' using hj
    exact ⟨q, (mem_partFamily _ _).mpr hq, (mem_partFamily _ _).mpr hq'⟩

/-- The dimensionwise product of higher categories, including the empty product. -/
def HigherCategory.product {J : Type v} (C : J → HigherCategory.{i, u} I) :
    HigherCategory I where
  carrier k := ∀ j, (C j).carrier k
  str.dim h k hk := CategoryStructure.product (fun j => (C j).str.dim h k hk)
  str.compatible h k l hk kl := Compatible.product (fun j => (C j).str.compatible h k l hk kl)

/-- A projection from a dimensionwise product. -/
def HigherCategory.projection {J : Type v} (C : J → HigherCategory.{i, u} I) (j : J) :
    Functor (HigherCategory.product C) (C j) where
  toFun _ x := x j
  map_source _ _ _ _ := rfl
  map_target _ _ _ _ := rfl
  map_identity _ _ _ _ := rfl
  map_comp _ _ _ _ _ _ h := (mem_partFamily _ _).mp h j

/-- The higher functor determined by its projections. -/
def HigherCategory.productLift {J : Type v} {C : J → HigherCategory.{i, u} I}
    {D : HigherCategory.{i, u} I} (f : ∀ j, Functor D (C j)) :
    Functor D (HigherCategory.product C) where
  toFun k x j := (f j).toFun k x
  map_source j k h x := funext (fun t => (f t).map_source j k h x)
  map_target j k h x := funext (fun t => (f t).map_target j k h x)
  map_identity j k h x := funext (fun t => (f t).map_identity j k h x)
  map_comp j k h x y z hz := (mem_partFamily _ _).mpr
    (fun t => (f t).map_comp j k h x y z hz)

/-- The fan of product projections. -/
def HigherCategory.productFan {J : Type u} (C : J → HigherCategory.{i, u} I) :
    Limits.Fan C := Limits.Fan.mk (HigherCategory.product C) (HigherCategory.projection C)

/-- The dimensionwise product satisfies the categorical universal property. -/
def HigherCategory.productIsLimit {J : Type u} (C : J → HigherCategory.{i, u} I) :
    Limits.IsLimit (HigherCategory.productFan C) :=
  Limits.Fan.IsLimit.mk _ (fun c => HigherCategory.productLift c.proj) (fun _ _ => rfl) (by
    intro c m hm
    apply Functor.ext
    funext k x j
    exact congrArg (fun f : c.pt ⟶ C j => f.toFun k x) (hm j))

/-! ## Finite and natural dimensions -/

/-- A heterogeneous $n$-category has dimensions $0,\ldots,n$. -/
abbrev NCategory (n : ℕ) := HigherCategory (Fin (n + 1))

/-- In dimension $\omega$ every cell already has a dimension in its carrier. -/
abbrev OmegaCategory := HigherCategory.{0, u} ℕ

end CategorialAlgebras.Heterogeneous
