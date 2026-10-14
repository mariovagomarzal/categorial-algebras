import Stemma
import Mathlib.Data.Fintype.Lattice
import CategorialAlgebras.Compact.Restriction
import CategorialAlgebras.Compact.Algebra

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Compact ω-categorial algebras" =>

Section `SLimitSingleSet` of the draft uses the category $`\omega\mathsf{CatAlg}(\Sigma)` of $`S`-sorted
$`\omega`-categorial $`\Sigma`-algebras, defined (Definitions `DSingleSetOmegaCat` and `DOmegaCatAlg` of the draft) as $`\mathsf{nCatAlg}(\Sigma)` in Definition `DManySortedCatAlg`, with
compact $`\omega`-categories in place of compact $`n`-categories. Recall that in a compact $`\omega`-category every cell is a
$`k`-cell for some $`k \in \mathbb{N}`.

```lean
universe u v w

namespace CategorialAlgebras.Compact

open Signature

variable {S : Type u}
```

# Finite products

:::construction (label := "compact.pi-omega-category") (central := false) (title := "Finite products of compact ω-categories")
A finite product $`\prod_{j \in J} C_j` of compact $`\omega`-categories, with the
componentwise structure, is a compact $`\omega`-category: if each $`f_j` is a $`k_j`-cell, the
family $`(f_j)_{j \in J}` is a $`k`-cell for $`k = \max_j k_j`, since a $`k_j`-cell is a
$`k`-cell for every $`k \geq k_j`. In particular $`\mathsf{A}_{\mathbf{s}}` is a compact
$`\omega`-category for every $`S`-sorted compact $`\omega`-category $`\mathsf{A}` and every word
$`\mathbf{s}`.

```lean
instance OmegaCategory.pi {J : Type v} [Fintype J] {C : J → Type w}
    [∀ j, OmegaCategory (C j)] : OmegaCategory ((j : J) → C j) where
  toCategory := Category.pi
  is_cell f := by
    classical
    choose k hk using fun j => OmegaCategory.is_cell (f j)
    refine ⟨Finset.univ.sup k, funext fun j => ?_⟩
    exact cell_of_le (hk j) (Finset.le_sup (Finset.mem_univ j))
```
:::

```lean
example (A : S → Type w) [∀ s, OmegaCategory (A s)] (s : List S) :
    OmegaCategory (Arity A s) := inferInstance
```

# Algebras

:::definition (label := "compact.omega-cat-algebra") (central := false) (title := "Compact ω-categorial algebra")
Let $`(S, \Sigma)` be a many-sorted signature. A *compact* $`\omega`-*categorial*
$`\Sigma`-*algebra* is a pair $`(\mathsf{A}, F)` where $`\mathsf{A}` is an $`S`-sorted compact
$`\omega`-category and $`F` assigns to every operation symbol
$`\sigma \in \Sigma_{\mathbf{s}, s}` a compact $`\omega`-functor
$`F_\sigma = \sigma^{\mathsf{A}} \colon \mathsf{A}_{\mathbf{s}} \to \mathsf{A}_s`.

```lean
structure OmegaCatAlgebra (Sig : Signature.{u, v} S) where
  /-- The carrier: an `S`-sorted compact `ω`-category. -/
  carrier : S → Type w
  /-- The compact `ω`-category of each sort. -/
  [str : ∀ s, OmegaCategory (carrier s)]
  /-- The interpretation of each operation symbol, as a compact `ω`-functor. -/
  op : ∀ {w : List S} {s : S}, Sig w s → OmegaFunctor (Arity carrier w) (carrier s)
```
:::

```lean
attribute [instance] OmegaCatAlgebra.str

namespace OmegaCatAlgebra

variable {Sig : Signature.{u, v} S}

instance : CoeFun (OmegaCatAlgebra.{u, v, w} Sig) fun _ ↦ S → Type w := ⟨OmegaCatAlgebra.carrier⟩

attribute [coe] OmegaCatAlgebra.carrier
```

:::definition (label := "compact.omega-cat-algebra-hom") (central := false) (title := "Homomorphism of compact ω-categorial algebras")
A *homomorphism* from $`\boldsymbol{\mathsf{A}}` to $`\boldsymbol{\mathsf{B}}` is an $`S`-sorted
compact $`\omega`-functor $`H = (H_s)_{s \in S}` such that
$`H_s(\sigma^{\boldsymbol{\mathsf{A}}}((a_j)_{j})) = \sigma^{\boldsymbol{\mathsf{B}}}((H_{s_j}(a_j))_{j})`
for every $`\sigma \in \Sigma_{\mathbf{s}, s}` and every family of cells
$`(a_j)_{j} \in \mathsf{A}_{\mathbf{s}}`.

```lean
structure Hom (A B : OmegaCatAlgebra.{u, v, w} Sig) where
  /-- The compact `ω`-functor at each sort. -/
  map : ∀ s, OmegaFunctor (A s) (B s)
  /-- The functors commute with the operations. -/
  map_op : ∀ {w : List S} {s : S} (σ : Sig w s) (a : Arity A w),
    map s (A.op σ a) = B.op σ (fun j => map (w.get j) (a j))
```
:::

```lean
attribute [simp] Hom.map_op

namespace Hom

@[ext]
lemma ext {A B : OmegaCatAlgebra.{u, v, w} Sig} {H K : Hom A B} (h : ∀ s, H.map s = K.map s) :
    H = K := by
  cases H; cases K; congr; funext s; exact h s

/-- The identity homomorphism. -/
def id (A : OmegaCatAlgebra.{u, v, w} Sig) : Hom A A where
  map s := Functor.id (A s)
  map_op σ a := rfl

/-- The composite of two homomorphisms. -/
def comp {A B C : OmegaCatAlgebra.{u, v, w} Sig} (K : Hom B C) (H : Hom A B) : Hom A C where
  map s := Functor.comp (K.map s) (H.map s)
  map_op σ a := by
    change K.map _ (H.map _ (A.op σ a)) = _
    rw [H.map_op, K.map_op]
    rfl

end Hom
```

:::definition (label := "compact.omega-cat-alg") (central := false) (title := "The category ωCatAlg(Σ)")
Compact $`\omega`-categorial $`\Sigma`-algebras and their homomorphisms form a category
$`\omega\mathsf{CatAlg}(\Sigma)`.

```lean
instance category : CategoryTheory.Category.{max u w} (OmegaCatAlgebra.{u, v, w} Sig) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp H K := Hom.comp K H
  id_comp H := by ext s f; rfl
  comp_id H := by ext s f; rfl
  assoc H K L := by ext s f; rfl
```
:::

```lean
end OmegaCatAlgebra

end CategorialAlgebras.Compact
```
