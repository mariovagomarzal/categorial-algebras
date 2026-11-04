import Mathlib.CategoryTheory.Category.Basic
import CategorialAlgebras.Compact.Category

/-!
# Single-set functors

A single-set functor is a mapping between the sets of cells that preserves, at every dimension,
sources, targets and composition (Definitions `DSingleSetCat`, `DSingleSet2Cat` and `DSingleSetnCat` of the draft). As for the categories,
the definition is given once for every preordered set of dimensions, and ported from the
group's repository `higher_category_theory`.
-/

universe u u₁ u₂ u₃

namespace CategorialAlgebras.Compact

/-- Let $C$ and $D$ be single-set categories with dimensions in $I$. A *single-set functor* from $C$
to $D$ is a mapping $F \colon C \to D$ such that, for every $k \in I$,

1. (Ci) $F(\mathrm{sc}^{k} f) = \mathrm{sc}^{k}(F f)$ and $F(\mathrm{tg}^{k} f) = \mathrm{tg}^{k}(F f)$
   for every $f \in C$;
2. (Cii) $F(g \#^{k} f) = F g \#^{k} F f$ whenever $\mathrm{sc}^{k} g = \mathrm{tg}^{k} f$.

The right-hand side of (Cii) is defined by (Ci).
-/
structure Functor (Index : Type) [Preorder Index] (C : Type u₁) [Category Index C]
    (D : Type u₂) [Category Index D] where
  /-- The underlying mapping on cells. -/
  map : C → D
  /-- (Ci) The mapping preserves sources. -/
  map_sc_eq_sc_map : ∀ (k : Index) (f : C), map (sc k f) = sc k (map f) := by hcat_disch
  /-- (Ci) The mapping preserves targets. -/
  map_tg_eq_tg_map : ∀ (k : Index) (f : C), map (tg k f) = tg k (map f) := by hcat_disch
  /-- Auxiliary: the images of composable cells are composable. -/
  protected comp_map {k : Index} {f g : C} (sc_tg_gf : sc_is_tg k g f) :
      sc_is_tg k (map g) (map f) := calc
    sc k (map g)
    _ = map (sc k g) := (map_sc_eq_sc_map k g).symm
    _ = map (tg k f) := by rw [sc_tg_gf]
    _ = tg k (map f) := map_tg_eq_tg_map k f
  /-- (Cii) The mapping preserves composition. -/
  map_comp_eq_comp_map : ∀ {k : Index} {f g : C} (sc_tg_gf : sc_is_tg k g f),
      map (g ♯[k] f ← sc_tg_gf) = (map g) ♯[k] (map f) ← (comp_map sc_tg_gf) := by
    hcat_disch

attribute [simp] Functor.map_sc_eq_sc_map Functor.map_tg_eq_tg_map Functor.map_comp_eq_comp_map

namespace Functor

variable {Index : Type} [Preorder Index]
  {C : Type u₁} [Category Index C]
  {D : Type u₂} [Category Index D]
  {E : Type u₃} [Category Index E]

instance : CoeFun (Functor Index C D) fun _ ↦ C → D := ⟨fun F ↦ F.map⟩

attribute [coe] Functor.map

/-- Two single-set functors with the same underlying mapping are equal. -/
@[ext]
lemma ext {F G : Functor Index C D} (h : ∀ f, F f = G f) : F = G := by
  cases F; cases G; congr; funext f; exact h f

/-!
### Composition and identities

Single-set functors compose as mappings, and the identity mapping of a single-set category is a
single-set functor.
-/

@[simp]
def comp (G : Functor Index D E) (F : Functor Index C D) :
    Functor Index C E where
  map f := G (F f)
  map_sc_eq_sc_map := by
    intro k f
    calc
      G (F (sc k f))
      _ = G (sc k (F f)) := by rw [F.map_sc_eq_sc_map k f]
      _ = sc k (G (F f)) := G.map_sc_eq_sc_map k (F f)
  map_tg_eq_tg_map := by
    intro k f
    calc
      G (F (tg k f))
      _ = G (tg k (F f)) := by rw [F.map_tg_eq_tg_map k f]
      _ = tg k (G (F f)) := G.map_tg_eq_tg_map k (F f)
  map_comp_eq_comp_map := by
    intro k f g sc_tg_gf
    calc
      G (F (g ♯[k] f ← sc_tg_gf))
      _ = G ((F g) ♯[k] (F f) ← F.comp_map sc_tg_gf) := by rw [F.map_comp_eq_comp_map sc_tg_gf]
      _ = (G (F g)) ♯[k] (G (F f)) ← G.comp_map (F.comp_map sc_tg_gf) :=
        G.map_comp_eq_comp_map (F.comp_map sc_tg_gf)

@[simp]
def id (C : Type u₁) [Category Index C] : Functor Index C C where
  map f := f

@[inherit_doc] scoped[CategorialAlgebras.Compact] infixr:100 " ⊚ " => Functor.comp

@[inherit_doc] scoped[CategorialAlgebras.Compact] notation "idₛ" => Functor.id

end Functor

/-!
### Single-set n-functors

A *single-set* $n$-*functor* is a single-set functor between single-set $n$-categories, and a
*single-set* $\omega$-*functor* one between single-set $\omega$-categories.
-/

abbrev NFunctor (n : ℕ)
    (C : Type u₁) [NCategory n C]
    (D : Type u₂) [NCategory n D] :=
  Functor (Fin n) C D

abbrev OmegaFunctor
    (C : Type u₁) [OmegaCategory C]
    (D : Type u₂) [OmegaCategory D] :=
  Functor ℕ C D

/-!
## The categories of single-set categories
-/

structure Cat (Index : Type) [Preorder Index] where
  /-- Build a `Cat` from a carrier type with a `Category` instance. -/
  of ::
  /-- The underlying set of cells. -/
  carrier : Type u
  /-- The single-set categorial structure on the carrier. -/
  [str : Category Index carrier]

attribute [instance] Cat.str

instance {Index : Type} [Preorder Index] : CoeSort (Cat Index) (Type u) := ⟨Cat.carrier⟩

attribute [coe] Cat.carrier

/-!
### The category of single-set categories

Single-set categories with dimensions in $I$ and single-set functors form a category, with the
composition and identities defined above. For $I = n$ this is
the category $\mathsf{nCat}$ of single-set $n$-categories and single-set $n$-functors
(Definition `DSingleSetnCat` of the draft).
-/

instance Cat.category {Index : Type} [Preorder Index] :
    CategoryTheory.LargeCategory.{u} (Cat Index) where
  Hom C D := Functor Index C D
  comp F G := G ⊚ F
  id C := idₛ C

abbrev NCat (n : ℕ) := Cat.{u} (Fin n)

end CategorialAlgebras.Compact
