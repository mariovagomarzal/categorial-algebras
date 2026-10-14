import Stemma
import CategorialAlgebras.Signature
import CategorialAlgebras.Compact.Product

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Single-set n-categorial algebras" =>

A many-sorted $`n`-categorial algebra is a many-sorted algebra whose carrier of every sort is a
single-set $`n`-category and whose operations are single-set $`n`-functors (Definition `DManySortedCatAlg` of the
draft).

```lean
universe u v w

namespace CategorialAlgebras.Compact

open Signature

variable {S : Type u}
```

# Many-sorted single-set n-categories

An $`S`-*sorted single-set* $`n`-*category* is a family $`\mathsf{A} = (\mathsf{A}_s)_{s \in S}` of
single-set $`n`-categories, and an $`S`-*sorted single-set* $`n`-*functor* is a family of single-set
$`n`-functors, one for each sort. For a word $`\mathbf{s} \in S^{\star}`,
$`\mathsf{A}_{\mathbf{s}} = \prod_{j \in |\mathbf{s}|} \mathsf{A}_{s_j}` is a single-set
$`n`-category with the componentwise structure; for $`\mathbf{s} = \lambda` it is the final
single-set $`n`-category.

```lean
example (n : ℕ) (A : S → Type w) [∀ s, NCategory n (A s)] (s : List S) :
    NCategory n (Arity A s) := inferInstance
```

# Algebras

:::definition (label := "compact.cat-algebra") (central := true) (title := "Single-set n-categorial algebra")
Let $`(S, \Sigma)` be a many-sorted signature and $`n \in \mathbb{N}`. A *single-set*
$`n`-*categorial* $`\Sigma`-*algebra* is a pair $`(\mathsf{A}, F)` where $`\mathsf{A}` is an
$`S`-sorted single-set $`n`-category and $`F` assigns to every operation symbol
$`\sigma \in \Sigma_{\mathbf{s}, s}` a single-set $`n`-functor
$`F_\sigma = \sigma^{\mathsf{A}} \colon \mathsf{A}_{\mathbf{s}} \to \mathsf{A}_s`.

A constant $`\sigma \in \Sigma_{\lambda, s}` is a functor from the final single-set $`n`-category,
so it picks out a cell of $`\mathsf{A}_s` that is a $`k`-cell for every $`k \in n`, as the draft
says.

```lean
structure CatAlgebra (Sig : Signature.{u, v} S) (n : ℕ) where
  /-- The carrier: an `S`-sorted single-set `n`-category. -/
  carrier : S → Type w
  /-- The single-set `n`-category of each sort. -/
  [str : ∀ s, NCategory n (carrier s)]
  /-- The interpretation of each operation symbol, as a single-set `n`-functor. -/
  op : ∀ {w : List S} {s : S}, Sig w s → NFunctor n (Arity carrier w) (carrier s)
```
:::

```lean
attribute [instance] CatAlgebra.str

namespace CatAlgebra

variable {Sig : Signature.{u, v} S} {n : ℕ}

instance : CoeFun (CatAlgebra.{u, v, w} Sig n) fun _ ↦ S → Type w := ⟨CatAlgebra.carrier⟩

attribute [coe] CatAlgebra.carrier
```

:::definition (label := "compact.cat-algebra-hom") (central := false) (title := "Homomorphism of single-set n-categorial algebras")
Let $`\boldsymbol{\mathsf{A}} = (\mathsf{A}, F)` and $`\boldsymbol{\mathsf{B}} = (\mathsf{B}, G)`
be single-set $`n`-categorial $`\Sigma`-algebras. A *homomorphism* from $`\boldsymbol{\mathsf{A}}`
to $`\boldsymbol{\mathsf{B}}` is an $`S`-sorted single-set $`n`-functor
$`H = (H_s)_{s \in S}` from $`\mathsf{A}` to $`\mathsf{B}` such that, for every
$`\sigma \in \Sigma_{\mathbf{s}, s}` and every family of cells
$`(a_j)_{j \in |\mathbf{s}|} \in \mathsf{A}_{\mathbf{s}}`,
$$`H_s\big(\sigma^{\boldsymbol{\mathsf{A}}}((a_j)_{j})\big) = \sigma^{\boldsymbol{\mathsf{B}}}\big((H_{s_j}(a_j))_{j}\big).`

As Definition `DManySortedCatAlg` of the draft says, the equation is asked for all cells, the $`n`-cells
($`C_n = C`), and not only for the $`k`-cells with $`k \in n`, which are the cells of dimension
below $`n`: otherwise a homomorphism would say nothing about the cells of top dimension.

```lean
structure Hom (A B : CatAlgebra.{u, v, w} Sig n) where
  /-- The single-set `n`-functor at each sort. -/
  map : ∀ s, NFunctor n (A s) (B s)
  /-- The functors commute with the operations. -/
  map_op : ∀ {w : List S} {s : S} (σ : Sig w s) (a : Arity A w),
    map s (A.op σ a) = B.op σ (fun j => map (w.get j) (a j))
```
:::

```lean
attribute [simp] Hom.map_op

namespace Hom

@[ext]
lemma ext {A B : CatAlgebra.{u, v, w} Sig n} {H K : Hom A B} (h : ∀ s, H.map s = K.map s) :
    H = K := by
  cases H; cases K; congr; funext s; exact h s

/-- The identity homomorphism. -/
def id (A : CatAlgebra.{u, v, w} Sig n) : Hom A A where
  map s := Functor.id (A s)
  map_op σ a := rfl

/-- The composite of two homomorphisms. -/
def comp {A B C : CatAlgebra.{u, v, w} Sig n} (K : Hom B C) (H : Hom A B) : Hom A C where
  map s := Functor.comp (K.map s) (H.map s)
  map_op σ a := by
    change K.map _ (H.map _ (A.op σ a)) = _
    rw [H.map_op, K.map_op]
    rfl

end Hom
```

:::definition (label := "compact.cat-alg") (central := false) (title := "The category nCatAlg(Σ)")
Single-set $`n`-categorial $`\Sigma`-algebras and their homomorphisms form a category
$`\mathsf{nCatAlg}(\Sigma)`, with the sortwise composition and identities of single-set
$`n`-functors.

```lean
instance category : CategoryTheory.Category.{max u w} (CatAlgebra.{u, v, w} Sig n) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp H K := Hom.comp K H
  id_comp H := by ext s f; rfl
  comp_id H := by ext s f; rfl
  assoc H K L := by ext s f; rfl
```
:::

```lean
end CatAlgebra
```

# The single-set n-categorial signature

In the single-set presentation an $`n`-categorial algebra is also a partial algebra on its cells,
for a signature that adds to $`\Sigma` sources, targets and compositions of every dimension
below $`n`.

:::definition (label := "compact.signature") (central := false) (title := "The single-set n-categorial signature")
Let $`\Sigma` be an $`S`-sorted signature and $`n \in \mathbb{N}`. The *single-set*
$`n`-*categorial signature determined by* $`\Sigma`, $`\Sigma^{(n)}`, is the expansion of
$`\Sigma` obtained by adding, for every $`k \in n` and every $`s \in S`, two operation symbols
$`\mathrm{sc}^{k}_{s}` and $`\mathrm{tg}^{k}_{s}` of arity $`(s)` and coarity $`s`, the
$`k`-source and the $`k`-target, and an operation symbol $`\circ^{k}_{s}` of arity $`(s, s)`
and coarity $`s`, the $`k`-composition (Definition `DSigmaCatSingleSet` of the draft).

```lean
inductive CompactSignature (Sig : Signature.{u, v} S) (n : ℕ) : List S → S → Type (max u v)
  /-- An operation symbol of `Sig`. -/
  | op {w : List S} {s : S} (σ : Sig w s) : CompactSignature Sig n w s
  /-- The `k`-source at sort `s`. -/
  | sc (k : Fin n) (s : S) : CompactSignature Sig n [s] s
  /-- The `k`-target at sort `s`. -/
  | tg (k : Fin n) (s : S) : CompactSignature Sig n [s] s
  /-- The `k`-composition at sort `s`. -/
  | comp (k : Fin n) (s : S) : CompactSignature Sig n [s, s] s
```
:::

```lean
end CategorialAlgebras.Compact
```
