import CategorialAlgebras.Homogeneous.Category
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Algebras in homogeneous higher categories

An operation is a higher functor from the componentwise product indexed by its input
word. The empty word gives a terminal higher category. Homomorphisms are sorted higher
functors commuting with all operations.
-/

universe i u v w

namespace CategorialAlgebras
namespace Homogeneous

open CategoryTheory

variable {I : Type i} [LT I] {S : Type u} {sig : Signature.{u, v} S}

/-- A sorted family of homogeneous higher categories. -/
abbrev SortedCategory (I : Type i) [LT I] (S : Type u) := S → HigherCategory.{i, w} I

/-- A sorted higher functor is a family of higher functors, one at each sort. -/
abbrev SortedFunctor (A B : SortedCategory.{i, u, w} I S) := ∀ s, Functor (A s) (B s)

/-- The componentwise category indexed by the positions of an input word. -/
def wordProduct (A : SortedCategory.{i, u, w} I S) (a : List S) : HigherCategory I :=
  HigherCategory.product (fun j : Fin a.length => A (a.get j))

/-- The empty word has a unique cell, and hence is terminal. -/
theorem wordProduct_nil_unique (A : SortedCategory.{i, u, w} I S) :
    ∀ x y : (wordProduct A []).carrier, x = y := by
  intro x y
  funext j
  exact Fin.elim0 j

/-- The unique higher functor to the empty word product. -/
def toEmptyProduct (A : SortedCategory.{i, u, w} I S) (C : HigherCategory.{i, w} I) :
    Functor C (wordProduct A []) where
  toFun _ j := Fin.elim0 j
  map_source _ _ := wordProduct_nil_unique A _ _
  map_target _ _ := wordProduct_nil_unique A _ _
  map_comp _ _ _ _ _ := (mem_partFamily _ _).mpr (fun j => Fin.elim0 j)

/-- The functor to an empty word product is unique. -/
theorem toEmptyProduct_unique (A : SortedCategory.{i, u, w} I S)
    (C : HigherCategory.{i, w} I) (f : Functor C (wordProduct A [])) :
    f = toEmptyProduct A C := by
  apply Functor.ext
  funext x
  exact wordProduct_nil_unique A _ _

/-- An algebra whose carriers are higher categories and whose operations are higher functors. -/
structure CategorialAlgebra (I : Type i) [LT I] {S : Type u} (sig : Signature.{u, v} S) where
  /-- A higher category at each sort. -/
  sort : SortedCategory.{i, u, w} I S
  /-- Every symbol is interpreted by a total higher functor. -/
  op : ∀ {a s}, sig a s → Functor (wordProduct sort a) (sort s)

namespace CategorialAlgebra

/-- The underlying sorted set of all cells. -/
abbrev carrier (A : CategorialAlgebra.{i, u, v, w} I sig) : S → Type w :=
  fun s => (A.sort s).carrier

/-- A homomorphism of categorial algebras. -/
@[ext] structure Hom (A B : CategorialAlgebra.{i, u, v, w} I sig) where
  /-- A higher functor at each sort. -/
  sort : ∀ s, Functor (A.sort s) (B.sort s)
  /-- The sorted functors commute with every operation. -/
  map_op : ∀ {a s} (σ : sig a s) (x : Word.Family A.carrier a),
    (sort s).toFun ((A.op σ).toFun x) =
      (B.op σ).toFun (fun j => (sort _).toFun (x j))

/-- The identity categorial homomorphism. -/
def Hom.id (A : CategorialAlgebra.{i, u, v, w} I sig) : Hom A A where
  sort s := Functor.id (A.sort s)
  map_op _ _ := rfl

/-- Composition of categorial homomorphisms. -/
def Hom.comp {A B C : CategorialAlgebra.{i, u, v, w} I sig}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  sort s := (f.sort s).comp (g.sort s)
  map_op σ x := by
    change (g.sort _).toFun ((f.sort _).toFun _) = _
    rw [f.map_op, g.map_op]
    rfl

/-- Categorial algebras and their homomorphisms form a category. -/
instance : Category (CategorialAlgebra.{i, u, v, w} I sig) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Forget the higher category structures and retain the total algebra. -/
def toAlgebra (A : CategorialAlgebra.{i, u, v, w} I sig) : Algebra sig where
  carrier := A.carrier
  op σ := (A.op σ).toFun

/-- Every cell of every sort has finite dimension. -/
def FiniteDimensional (A : CategorialAlgebra.{0, u, v, w} ℕ sig) : Prop :=
  ∀ s, (A.sort s).FiniteDimensional

end CategorialAlgebra

/-- The category of homogeneous $n$-categorial algebras. -/
abbrev NCategorialAlgebra (n : ℕ) {S : Type u} (sig : Signature.{u, v} S) :=
  CategorialAlgebra.{0, u, v, w} (Fin n) sig

/-- The full category of homogeneous $\omega$-categorial algebras. -/
abbrev OmegaCategorialAlgebra {S : Type u} (sig : Signature.{u, v} S) :=
  ObjectProperty.FullSubcategory
    (CategorialAlgebra.FiniteDimensional :
      ObjectProperty (CategorialAlgebra.{0, u, v, w} ℕ sig))

end Homogeneous
end CategorialAlgebras
