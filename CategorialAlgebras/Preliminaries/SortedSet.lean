import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Function

/-!
# Sorted sets

An $S$-sorted set is a family of types. Its category is Mathlib's pointwise category on
$S \to \mathsf{Type}$. Subsets and their set operations are taken componentwise.
-/

universe u v w

namespace CategorialAlgebras

open CategoryTheory

/-- An $S$-sorted set with carriers in `Type w`. -/
abbrev SortedSet (S : Type u) := S → Type w

namespace SortedSet

/-! ## Sorted subsets and mappings -/

/-- A sorted mapping, written as a family of functions. -/
abbrev Map {S : Type u} (A : S → Type v) (B : S → Type w) := ∀ s, A s → B s

/-- A sorted subset of $A$. Pointwise set operations give its complete lattice. -/
abbrev Subset {S : Type u} (A : SortedSet.{u, w} S) := ∀ s, Set (A s)

/-- The sorted set underlying a sorted subset. -/
abbrev Subset.carrier {S : Type u} {A : SortedSet.{u, w} S} (U : Subset A) :=
  fun s => {a : A s // a ∈ U s}

/-- Regard a family of functions as a morphism in the pointwise category. -/
def homOfMap {S : Type u} {A B : SortedSet.{u, w} S} (f : Map A B) : A ⟶ B :=
  fun s => TypeCat.ofHom (f s)

/-- A sorted mapping factors uniquely through a subset exactly when its image lies in it.
The factor is assembled from Mathlib's `Set.codRestrict`. -/
theorem range_subset_iff_exists_unique {S : Type u} {A : S → Type v} {B : S → Type w}
    (f : Map A B) (U : Subset B) :
    (∀ s, Set.range (f s) ⊆ U s) ↔
      ∃! h : Map A U.carrier, ∀ s x, (h s x).val = f s x := by
  constructor
  · intro h
    refine ⟨fun s => Set.codRestrict (f s) (U s) (fun x => h s ⟨x, rfl⟩),
      fun _ _ => rfl, ?_⟩
    intro g hg
    funext s x
    exact Subtype.ext (hg s x)
  · rintro ⟨h, hh, _⟩ s y ⟨x, rfl⟩
    rw [← hh s x]
    exact (h s x).property

/-! ## Change of sorts -/

/-- Change of sorts $\Delta_\varphi$, using Mathlib's precomposition functor. -/
def delta {S : Type u} {T : Type v} (φ : S → T) :
    SortedSet.{v, w} T ⥤ SortedSet.{u, w} S :=
  CategoryTheory.Pi.comap (fun _ : T => Type w) φ

end SortedSet
end CategorialAlgebras
