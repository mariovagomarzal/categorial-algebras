import Stemma
import CategorialAlgebras.Extended.Algebra

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Extended ω-categorial algebras" =>

Section 10 of the draft uses the category
$`\omega\mathsf{Cat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)` of extended $`\omega`-categorial algebras,
defined in Definition 6.6 of the draft (labelled `DOmegaExtCatAlg`) exactly as the extended
$`n`-categorial algebras of Definition 6.3, with extended $`\omega`-categories in place of
extended $`n`-categories.

```lean
universe u v w

namespace CategorialAlgebras.Extended

variable {S : Type u}
```

:::definition (label := "extended.omega-cat-algebra") (central := false) (title := "Extended ω-categorial algebra")
Let $`(S, \Sigma)` be a many-sorted signature. An *extended* $`\omega`-*categorial*
$`\Sigma`-*algebra* is a pair $`(\mathsf{A}, F)` where $`\mathsf{A}` is an $`S`-sorted extended
$`\omega`-category and $`F` assigns to every operation symbol
$`\sigma \in \Sigma_{\mathbf{s}, s}` an extended $`\omega`-functor
$`F_\sigma = \sigma^{\mathsf{A}} \colon \mathsf{A}_{\mathbf{s}} \to \mathsf{A}_s`.

```lean
structure OmegaCatAlgebra (Sig : Signature.{u, v} S) where
  /-- The carrier: an `S`-sorted extended `ω`-category. -/
  carrier : S → OmegaTypeFamily.{w}
  /-- The extended `ω`-category of each sort. -/
  [str : ∀ s, OmegaCategory (carrier s)]
  /-- The interpretation of each operation symbol, as an extended `ω`-functor. -/
  op : ∀ {w : List S} {s : S}, Sig w s → OmegaFunctor (ExtArity carrier w) (carrier s)
```
:::

```lean
attribute [instance] OmegaCatAlgebra.str

namespace OmegaCatAlgebra

variable {Sig : Signature.{u, v} S}

instance : CoeFun (OmegaCatAlgebra.{u, v, w} Sig) fun _ ↦ S → OmegaTypeFamily.{w} :=
  ⟨OmegaCatAlgebra.carrier⟩

attribute [coe] OmegaCatAlgebra.carrier
```

:::definition (label := "extended.omega-cat-algebra-hom") (central := false) (title := "Homomorphism of extended ω-categorial algebras")
A *homomorphism* from $`\boldsymbol{\mathsf{A}}` to $`\boldsymbol{\mathsf{B}}` is an $`S`-sorted
extended $`\omega`-functor $`H = (H_s)_{s \in S}` from $`\mathsf{A}` to $`\mathsf{B}` such
that, for every $`\sigma \in \Sigma_{\mathbf{s}, s}`, every dimension $`k \in \mathbb{N}` and
every family of $`k`-cells $`(a_j)_{j \in |\mathbf{s}|} \in \mathsf{A}_{\mathbf{s}}`,
$$`H_s\big(\sigma^{\boldsymbol{\mathsf{A}}}((a_j)_{j})\big) = \sigma^{\boldsymbol{\mathsf{B}}}\big((H_{s_j}(a_j))_{j}\big).`

```lean
structure Hom (A B : OmegaCatAlgebra.{u, v, w} Sig) where
  /-- The extended `ω`-functor at each sort. -/
  map : ∀ s, OmegaFunctor (A s) (B s)
  /-- The functors commute with the operations, in every dimension. -/
  map_op : ∀ {w : List S} {s : S} (σ : Sig w s) (k : ℕ) (a : ExtArity A w k),
    map s k (A.op σ k a) = B.op σ k (fun j => map (w.get j) k (a j))
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
  map_op σ k a := rfl

/-- The composite of two homomorphisms. -/
def comp {A B C : OmegaCatAlgebra.{u, v, w} Sig} (K : Hom B C) (H : Hom A B) : Hom A C where
  map s := Functor.comp (K.map s) (H.map s)
  map_op σ k a := by
    change K.map _ k (H.map _ k (A.op σ k a)) = _
    rw [H.map_op, K.map_op]
    rfl

end Hom
```

:::definition (label := "extended.omega-cat-alg") (central := false) (title := "The category ωCatᵉˣᵗAlg(Σ)")
Extended $`\omega`-categorial $`\Sigma`-algebras and their homomorphisms form a category
$`\omega\mathsf{Cat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)`, with the sortwise composition and
identities of extended $`\omega`-functors.

```lean
instance category : CategoryTheory.Category.{max u w} (OmegaCatAlgebra.{u, v, w} Sig) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp H K := Hom.comp K H
  id_comp H := by ext s k f; rfl
  comp_id H := by ext s k f; rfl
  assoc H K L := by ext s k f; rfl
```
:::

```lean
end OmegaCatAlgebra

end CategorialAlgebras.Extended
```
