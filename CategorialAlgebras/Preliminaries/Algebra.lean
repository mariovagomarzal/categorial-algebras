import CategorialAlgebras.Preliminaries.Word

/-!
# Algebras for sorted signatures

A signature assigns a type of symbols to every input word and output sort. Algebras have
arbitrary carrier universes; homomorphisms preserve all operations, including constants.
-/

universe u v w w' w''

namespace CategorialAlgebras

open CategoryTheory

/-- An $S$-sorted signature. -/
abbrev Signature (S : Type u) := List S → S → Type v

/-- A many-sorted signature, with sorts in `Type u` and symbols in `Type v`.
Fixing these two universes gives a category of signatures and derivors. -/
structure ManySortedSignature where
  /-- The type of sorts. -/
  sort : Type u
  /-- The operation symbols at each input word and output sort. -/
  symbol : Signature.{u, v} sort

/-- A total algebra for a many-sorted signature $\Sigma$. -/
structure Algebra {S : Type u} (sig : Signature.{u, v} S) where
  /-- The carrier at each sort. -/
  carrier : S → Type w
  /-- Interpretation of an operation on a family of arguments. -/
  op : ∀ {a s}, sig a s → Word.Family carrier a → carrier s

namespace Algebra

/-! ## Homomorphisms and the category of algebras -/

variable {S : Type u} {sig : Signature.{u, v} S}

/-- A homomorphism preserves the interpretation of every operation. -/
@[ext] structure Hom (A : Algebra.{u, v, w} sig) (B : Algebra.{u, v, w'} sig) where
  /-- The underlying sorted mapping. -/
  toMap : SortedSet.Map A.carrier B.carrier
  /-- Preservation of operations. -/
  map_op : ∀ {a s} (σ : sig a s) (x : Word.Family A.carrier a),
    toMap s (A.op σ x) = B.op σ (fun j => toMap _ (x j))

/-- The identity homomorphism. -/
def Hom.id (A : Algebra.{u, v, w} sig) : Hom A A where
  toMap _ := _root_.id
  map_op _ _ := rfl

/-- Composition of homomorphisms, in diagrammatic order. -/
def Hom.comp {A : Algebra.{u, v, w} sig} {B : Algebra.{u, v, w'} sig}
    {C : Algebra.{u, v, w''} sig} (f : Hom A B) (g : Hom B C) : Hom A C where
  toMap s x := g.toMap s (f.toMap s x)
  map_op σ x := by rw [f.map_op, g.map_op]

/-- Algebras with carriers in a fixed universe form a category. -/
instance : Category (Algebra.{u, v, w} sig) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The forgetful functor to Mathlib's category of sorted sets. -/
def forget (sig : Signature.{u, v} S) : Algebra.{u, v, w} sig ⥤ SortedSet.{u, w} S where
  obj A := A.carrier
  map f := SortedSet.homOfMap f.toMap
  map_id _ := rfl
  map_comp _ _ := rfl

end Algebra
end CategorialAlgebras
