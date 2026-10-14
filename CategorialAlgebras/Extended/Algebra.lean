import Stemma
import CategorialAlgebras.Signature
import CategorialAlgebras.Extended.Product

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Extended n-categorial algebras" =>

An extended $`n`-categorial algebra is a many-sorted algebra whose carrier of every sort is an
extended $`n`-category and whose operations are extended $`n`-functors (Definitions `DSortednCatGl` and `DGlCatAlg`
of the draft).

```lean
universe u v w

namespace CategorialAlgebras.Extended

variable {S : Type u}
```

# Many-sorted extended n-categories

An $`S`-*sorted extended* $`n`-*category* is a family $`\mathsf{A} = (\mathsf{A}_s)_{s \in S}`
of extended $`n`-categories, and an $`S`-*sorted extended* $`n`-*functor* a family of extended
$`n`-functors, one for each sort (Definition `DSortednCatGl` of the draft). For a word
$`\mathbf{s} \in S^{\star}`, $`\mathsf{A}_{\mathbf{s}} = \prod_{j \in |\mathbf{s}|} \mathsf{A}_{s_j}`
is an extended $`n`-category, whose $`k`-cells are the families of $`k`-cells.

:::definition (label := "extended.arity-product") (central := false) (title := "Products along a word")
For an $`S`-sorted family $`\mathsf{A}` of extended categories and a word
$`\mathbf{s} \in S^{\star}`, $`\mathsf{A}_{\mathbf{s}}` is the product of the
$`\mathsf{A}_{s_j}`: its $`k`-cells are the families $`(a_j)_{j \in |\mathbf{s}|}` of $`k`-cells
$`a_j \in (\mathsf{A}_{s_j})_k`.

```lean
abbrev ExtArity {Index : Type} (A : S → TypeFamily.{w} Index) (s : List S) :
    TypeFamily.{w} Index :=
  fun k => (j : Fin s.length) → A (s.get j) k
```
:::

```lean
example (n : ℕ) (A : S → NTypeFamily.{w} n) [∀ s, NCategory n (A s)] (s : List S) :
    NCategory n (ExtArity A s) := inferInstance
```

# Algebras

:::definition (label := "extended.cat-algebra") (central := true) (title := "Extended n-categorial algebra")
Let $`(S, \Sigma)` be a many-sorted signature and $`n \in \mathbb{N}`. An *extended*
$`n`-*categorial* $`\Sigma`-*algebra* is a pair $`(\mathsf{A}, F)` where $`\mathsf{A}` is an
$`S`-sorted extended $`n`-category and $`F` assigns to every operation symbol
$`\sigma \in \Sigma_{\mathbf{s}, s}` an extended $`n`-functor
$`F_\sigma = \sigma^{\mathsf{A}} \colon \mathsf{A}_{\mathbf{s}} \to \mathsf{A}_s`.

```lean
structure CatAlgebra (Sig : Signature.{u, v} S) (n : ℕ) where
  /-- The carrier: an `S`-sorted extended `n`-category. -/
  carrier : S → NTypeFamily.{w} n
  /-- The extended `n`-category of each sort. -/
  [str : ∀ s, NCategory n (carrier s)]
  /-- The interpretation of each operation symbol, as an extended `n`-functor. -/
  op : ∀ {w : List S} {s : S}, Sig w s → NFunctor n (ExtArity carrier w) (carrier s)
```
:::

```lean
attribute [instance] CatAlgebra.str

namespace CatAlgebra

variable {Sig : Signature.{u, v} S} {n : ℕ}

instance : CoeFun (CatAlgebra.{u, v, w} Sig n) fun _ ↦ S → NTypeFamily.{w} n :=
  ⟨CatAlgebra.carrier⟩

attribute [coe] CatAlgebra.carrier
```

:::definition (label := "extended.cat-algebra-hom") (central := false) (title := "Homomorphism of extended n-categorial algebras")
A *homomorphism* from $`\boldsymbol{\mathsf{A}}` to $`\boldsymbol{\mathsf{B}}` is an $`S`-sorted
extended $`n`-functor $`H = (H_s)_{s \in S}` from $`\mathsf{A}` to $`\mathsf{B}` such that, for
every $`\sigma \in \Sigma_{\mathbf{s}, s}`, every dimension $`k \in n + 1` and every family of
$`k`-cells $`(a_j)_{j \in |\mathbf{s}|} \in \mathsf{A}_{\mathbf{s}}`,
$$`H_s\big(\sigma^{\boldsymbol{\mathsf{A}}}((a_j)_{j})\big) = \sigma^{\boldsymbol{\mathsf{B}}}\big((H_{s_j}(a_j))_{j}\big).`

As Definition `DGlCatAlg` of the draft says, the equation is asked for every $`k \in n + 1`, including
the $`n`-cells, the top dimension of an extended $`n`-category.

```lean
structure Hom (A B : CatAlgebra.{u, v, w} Sig n) where
  /-- The extended `n`-functor at each sort. -/
  map : ∀ s, NFunctor n (A s) (B s)
  /-- The functors commute with the operations, in every dimension. -/
  map_op : ∀ {w : List S} {s : S} (σ : Sig w s) (k : FinSucc n) (a : ExtArity A w k),
    map s k (A.op σ k a) = B.op σ k (fun j => map (w.get j) k (a j))
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
  map_op σ k a := rfl

/-- The composite of two homomorphisms. -/
def comp {A B C : CatAlgebra.{u, v, w} Sig n} (K : Hom B C) (H : Hom A B) : Hom A C where
  map s := Functor.comp (K.map s) (H.map s)
  map_op σ k a := by
    change K.map _ k (H.map _ k (A.op σ k a)) = _
    rw [H.map_op, K.map_op]
    rfl

end Hom
```

:::definition (label := "extended.cat-alg") (central := false) (title := "The category nCatᵉˣᵗAlg(Σ)")
Extended $`n`-categorial $`\Sigma`-algebras and their homomorphisms form a category
$`\mathsf{nCat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)`.

```lean
instance category : CategoryTheory.Category.{max u w} (CatAlgebra.{u, v, w} Sig n) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp H K := Hom.comp K H
  id_comp H := by ext s k f; rfl
  comp_id H := by ext s k f; rfl
  assoc H K L := by ext s k f; rfl
```
:::

```lean
end CatAlgebra
```

# The extended n-categorial signature

:::definition (label := "extended.signature") (central := false) (title := "The extended n-categorial signature")
Let $`\Sigma` be an $`S`-sorted signature and $`n \in \mathbb{N}`. The *extended*
$`n`-*categorial signature determined by* $`\Sigma`, $`\Sigma^{\mathrm{ext}(n)}`, has sorts
$`(n + 1) \times S`, the sort $`(k, s)` standing for the $`k`-cells of sort $`s`, and the
following operation symbols (Definition `DSigmaCatGlobular` of the draft):

1. for every $`k \in n + 1` and $`\sigma \in \Sigma_{\mathbf{s}, s}`, a copy $`\sigma_k` of arity
   $`(k, \mathbf{s}) = ((k, s_j))_{j \in |\mathbf{s}|}` and coarity $`(k, s)`;
2. for all $`j < k` in $`n + 1` and $`s \in S`, the $`(j,k)`-source and the $`(j,k)`-target
   $`\mathrm{sc}^{(j,k)}_s, \mathrm{tg}^{(j,k)}_s` of arity $`((k, s))` and coarity $`(j, s)`,
   the $`(k,j)`-identity $`\mathrm{i}^{(k,j)}_s` of arity $`((j, s))` and coarity $`(k, s)`, and
   the $`j`-composition of $`k`-cells $`\circ^{(j,k)}_s` of arity $`((k, s), (k, s))` and
   coarity $`(k, s)`.

The draft defines it by cases on the arity; as an inductive family the symbols are exactly the
disjoint union of the cases.

```lean
inductive ExtendedSignature (Sig : Signature.{u, v} S) (n : ℕ) :
    List (FinSucc n × S) → FinSucc n × S → Type (max u v)
  /-- The copy acting on `k`-cells of an operation symbol of `Sig`. -/
  | op (k : FinSucc n) {w : List S} {s : S} (σ : Sig w s) :
      ExtendedSignature Sig n (w.map fun t => (k, t)) (k, s)
  /-- The `(j,k)`-source at sort `s`. -/
  | sc {j k : FinSucc n} (h : j < k) (s : S) : ExtendedSignature Sig n [(k, s)] (j, s)
  /-- The `(j,k)`-target at sort `s`. -/
  | tg {j k : FinSucc n} (h : j < k) (s : S) : ExtendedSignature Sig n [(k, s)] (j, s)
  /-- The `(k,j)`-identity at sort `s`. -/
  | idm {j k : FinSucc n} (h : j < k) (s : S) : ExtendedSignature Sig n [(j, s)] (k, s)
  /-- The `j`-composition of `k`-cells at sort `s`. -/
  | comp {j k : FinSucc n} (h : j < k) (s : S) :
      ExtendedSignature Sig n [(k, s), (k, s)] (k, s)
```
:::

```lean
end CategorialAlgebras.Extended
```
