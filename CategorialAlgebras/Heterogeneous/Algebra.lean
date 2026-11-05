import CategorialAlgebras.Heterogeneous.Category
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Algebras in heterogeneous higher categories

An operation is a higher functor from the componentwise product indexed by its input
word. The empty word gives a terminal higher category. Homomorphisms are sorted higher
functors commuting with all operations.
-/

universe i u v w

namespace CategorialAlgebras
namespace Heterogeneous

open CategoryTheory

variable {I : Type i} [Preorder I] {S : Type u} {sig : Signature.{u, v} S}

/-! ## Sorted categories and word products -/

/-- A sorted family of heterogeneous higher categories. -/
abbrev SortedCategory (I : Type i) [Preorder I] (S : Type u) := S → HigherCategory.{i, w} I

/-- A sorted higher functor is a family of higher functors, one at each sort. -/
abbrev SortedFunctor (A B : SortedCategory.{i, u, w} I S) := ∀ s, Functor (A s) (B s)

/-- The componentwise category indexed by the positions of an input word. -/
def wordProduct (A : SortedCategory.{i, u, w} I S) (a : List S) : HigherCategory I :=
  HigherCategory.product (fun j : Fin a.length => A (a.get j))

/-- The empty word has a unique cell, and hence is terminal. -/
theorem wordProduct_nil_unique (A : SortedCategory.{i, u, w} I S) :
    ∀ (k : I), ∀ x y : (wordProduct A []).carrier k, x = y := by
  intro k x y
  funext j
  exact Fin.elim0 j

/-- The unique higher functor to the empty word product. -/
def toEmptyProduct (A : SortedCategory.{i, u, w} I S) (C : HigherCategory.{i, w} I) :
    Functor C (wordProduct A []) where
  toFun _ _ j := Fin.elim0 j
  map_source _ _ _ _ := wordProduct_nil_unique A _ _ _
  map_target _ _ _ _ := wordProduct_nil_unique A _ _ _
  map_identity _ _ _ _ := wordProduct_nil_unique A _ _ _
  map_comp _ _ _ _ _ _ _ := (mem_partFamily _ _).mpr (fun j => Fin.elim0 j)

/-- The functor to an empty word product is unique. -/
theorem toEmptyProduct_unique (A : SortedCategory.{i, u, w} I S)
    (C : HigherCategory.{i, w} I) (f : Functor C (wordProduct A [])) :
    f = toEmptyProduct A C := by
  apply Functor.ext
  funext k x
  exact wordProduct_nil_unique A _ _ _

/-! ## Categorial algebras and homomorphisms -/

/-- An algebra whose carriers are higher categories and whose operations are higher functors. -/
structure CategorialAlgebra (I : Type i) [Preorder I] {S : Type u} (sig : Signature.{u, v} S) where
  /-- A higher category at each sort. -/
  sort : SortedCategory.{i, u, w} I S
  /-- Every symbol is interpreted by a total higher functor. -/
  op : ∀ {a s}, sig a s → Functor (wordProduct sort a) (sort s)

namespace CategorialAlgebra

/-- The underlying sorted set of all cells. -/
abbrev carrier (A : CategorialAlgebra.{i, u, v, w} I sig) : I × S → Type w :=
  fun s => (A.sort s.2).carrier s.1

/-- A homomorphism of categorial algebras. -/
@[ext] structure Hom (A B : CategorialAlgebra.{i, u, v, w} I sig) where
  /-- A higher functor at each sort. -/
  sort : ∀ s, Functor (A.sort s) (B.sort s)
  /-- The sorted functors commute with every operation. -/
  map_op : ∀ {a s} (σ : sig a s) (k : I) (x : Word.Family (fun s => A.carrier (k, s)) a),
    (sort s).toFun k ((A.op σ).toFun k x) =
      (B.op σ).toFun k (fun j => (sort _).toFun k (x j))

/-- The identity categorial homomorphism. -/
def Hom.id (A : CategorialAlgebra.{i, u, v, w} I sig) : Hom A A where
  sort s := Functor.id (A.sort s)
  map_op _ _ _ := rfl

/-- Composition of categorial homomorphisms. -/
def Hom.comp {A B C : CategorialAlgebra.{i, u, v, w} I sig}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  sort s := (f.sort s).comp (g.sort s)
  map_op σ k x := by
    change (g.sort _).toFun k ((f.sort _).toFun k _) = _
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

/-- Forget the higher structure at a chosen dimension. -/
def toAlgebra (A : CategorialAlgebra.{i, u, v, w} I sig) (k : I) : Algebra sig where
  carrier s := A.carrier (k, s)
  op σ := (A.op σ).toFun k

end CategorialAlgebra

/-- The category of heterogeneous $n$-categorial algebras. -/
abbrev NCategorialAlgebra (n : ℕ) {S : Type u} (sig : Signature.{u, v} S) :=
  CategorialAlgebra.{0, u, v, w} (Fin (n + 1)) sig

/-- The category of heterogeneous $\omega$-categorial algebras. -/
abbrev OmegaCategorialAlgebra {S : Type u} (sig : Signature.{u, v} S) :=
  CategorialAlgebra.{0, u, v, w} ℕ sig

end Heterogeneous
end CategorialAlgebras
