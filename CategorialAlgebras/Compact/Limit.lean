import Stemma
import Mathlib.CategoryTheory.Equivalence
import CategorialAlgebras.Compact.Truncation

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "ωCatAlg(Σ) as a pseudo-limit" =>

Proposition `PUnivPropCatAlg` of the draft states that $`\omega\mathsf{CatAlg}(\Sigma)`, with the
truncation functors $`T^{(n,\omega)}_{\Sigma}`, is the projective limit of the categories
$`\mathsf{nCatAlg}(\Sigma)` and the truncation functors $`T^{(m,n)}_{\Sigma}`. In the compact
presentation these functors compose only up to the canonical isomorphisms of Proposition
`compact.truncation-proj-system`: a cell of a truncation is a cell together with the proof that it
has the right dimension, and truncating twice nests these proofs. The equations
$`T^{(m,n)}_{\Sigma} \circ T^{(n,\omega)}_{\Sigma} = T^{(m,\omega)}_{\Sigma}` fail already for the
projections themselves, so the strict universal property cannot be stated faithfully.

This document states it as a *pseudo-limit*: compatible families are compatible up to specified
isomorphisms, and the universal property says that $`\omega\mathsf{CatAlg}(\Sigma)` is equivalent
to the category of these families, through its truncations. This is the form in which the draft
uses the universal property (Corollary `CLimitNat`), and it agrees with the strict one wherever the
latter makes sense. For a tower indexed by $`\mathbb{N}`, it is enough to give the isomorphisms
between consecutive levels: those between any two levels are their composites, and no coherence
condition is needed.

```lean
universe u v w

namespace CategorialAlgebras.Compact

open CategoryTheory

variable {S : Type u} (Sig : Signature.{u, v} S)
```

# Compatible families

:::definition (label := "compact.compatible-family") (central := false) (title := "Compatible families")
A *compatible family* of compact categorial $`\Sigma`-algebras is a family
$`(\boldsymbol{\mathsf{A}}_n)_{n \in \mathbb{N}}`, with $`\boldsymbol{\mathsf{A}}_n` a compact
$`n`-categorial $`\Sigma`-algebra, together with isomorphisms
$`\varphi_n \colon T^{(n,n+1)}_{\Sigma}(\boldsymbol{\mathsf{A}}_{n+1}) \cong \boldsymbol{\mathsf{A}}_n`.
A *morphism* of compatible families from $`(\boldsymbol{\mathsf{A}}_n, \varphi_n)` to
$`(\boldsymbol{\mathsf{B}}_n, \psi_n)` is a family of homomorphisms
$`H_n \colon \boldsymbol{\mathsf{A}}_n \to \boldsymbol{\mathsf{B}}_n` such that
$`\psi_n \circ T^{(n,n+1)}_{\Sigma}(H_{n+1}) = H_n \circ \varphi_n` for every $`n`. With the
levelwise composition and identities, compatible families form a category, the pseudo-limit of the
categories $`\mathsf{nCatAlg}(\Sigma)` along the truncation functors.

In the draft, a compatible family is one with
$`T^{(m,n)}_{\Sigma}(\boldsymbol{\mathsf{A}}_n) = \boldsymbol{\mathsf{A}}_m`, and a morphism one with
$`T^{(m,n)}_{\Sigma}(H_n) = H_m`; here the equalities are replaced by the isomorphisms $`\varphi_n`.

```lean
structure CompatibleFamily where
  /-- The compact `n`-categorial algebra at level `n`. -/
  alg : ∀ n, CatAlgebra.{u, v, w} Sig n
  /-- The truncation of level `n + 1` is level `n`, up to isomorphism. -/
  iso : ∀ n, (truncation Sig (Nat.le_succ n)).obj (alg (n + 1)) ≅ alg n

namespace CompatibleFamily

variable {Sig}

@[ext]
structure Hom (A B : CompatibleFamily.{u, v, w} Sig) where
  /-- The homomorphism at level `n`. -/
  map : ∀ n, A.alg n ⟶ B.alg n
  /-- The homomorphisms commute with the isomorphisms of the families. -/
  comm : ∀ n, (truncation Sig (Nat.le_succ n)).map (map (n + 1)) ≫ (B.iso n).hom =
    (A.iso n).hom ≫ map n

instance category : CategoryTheory.Category.{max u w} (CompatibleFamily.{u, v, w} Sig) where
  Hom A B := Hom A B
  id A := ⟨fun n => 𝟙 (A.alg n), fun n => by simp⟩
  comp H K := ⟨fun n => H.map n ≫ K.map n, fun n => by
    rw [Functor.map_comp, CategoryTheory.Category.assoc, K.comm,
      ← CategoryTheory.Category.assoc, H.comm, CategoryTheory.Category.assoc]⟩
  id_comp _ := Hom.ext (funext fun _ => CategoryTheory.Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => CategoryTheory.Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => CategoryTheory.Category.assoc _ _ _)

end CompatibleFamily
```
:::

# The family of truncations

:::definition (label := "compact.trunc-family") (central := false) (title := "The family of truncations")
The truncations $`(T^{(n,\omega)}_{\Sigma}(\boldsymbol{\mathsf{B}}))_{n \in \mathbb{N}}` of a compact
$`\omega`-categorial $`\Sigma`-algebra $`\boldsymbol{\mathsf{B}}`, with the canonical isomorphisms
$`T^{(n,n+1)}_{\Sigma}(T^{(n+1,\omega)}_{\Sigma}(\boldsymbol{\mathsf{B}})) \cong
T^{(n,\omega)}_{\Sigma}(\boldsymbol{\mathsf{B}})` of Proposition `compact.truncation-proj-system`, are a
compatible family, and the truncations of a homomorphism are a morphism of compatible families, by
the naturality of these isomorphisms. This is a functor from $`\omega\mathsf{CatAlg}(\Sigma)` to the
category of compatible families.

```lean
def truncFamilies : OmegaCatAlgebra.{u, v, w} Sig ⥤ CompatibleFamily.{u, v, w} Sig where
  obj B :=
    { alg := fun n => (truncationω Sig n).obj B
      iso := fun n => (truncationω_comp_iso Sig (Nat.le_succ n)).app B }
  map H :=
    { map := fun n => (truncationω Sig n).map H
      comm := fun n => (truncationω_comp_iso Sig (Nat.le_succ n)).hom.naturality H }
  map_id _ := rfl
  map_comp _ _ := rfl
```
:::

# The universal property

:::theorem (label := "compact.omega-cat-alg-pseudo-limit") (central := false) (title := "ωCatAlg(Σ) is the pseudo-limit of the nCatAlg(Σ)")
For every many-sorted signature $`\Sigma`, the functor of truncations from
$`\omega\mathsf{CatAlg}(\Sigma)` to the category of compatible families is an equivalence of
categories. That is:

1. it is faithful and full: the homomorphisms $`\boldsymbol{\mathsf{A}} \to \boldsymbol{\mathsf{B}}`
   of compact $`\omega`-categorial $`\Sigma`-algebras correspond bijectively, through their
   truncations, to the morphisms between the families of truncations (Corollary `CLimitNat` of the
   draft, first part);
2. it is essentially surjective: every compatible family is isomorphic to the family of
   truncations of a compact $`\omega`-categorial $`\Sigma`-algebra, its limit.

This is Proposition `PUnivPropCatAlg` of the draft, up to isomorphism: a family of functors
$`F_n \colon \mathsf{L} \to \mathsf{nCatAlg}(\Sigma)` with natural isomorphisms
$`T^{(n,n+1)}_{\Sigma} \circ F_{n+1} \cong F_n` is a functor from $`\mathsf{L}` to the category of
compatible families, and thus factors through $`\omega\mathsf{CatAlg}(\Sigma)`, uniquely up to a
unique natural isomorphism.

```lean
theorem truncFamilies_isEquivalence : (truncFamilies.{u, v, w} Sig).IsEquivalence := by
  sorry
```
:::

```lean
end CategorialAlgebras.Compact
```
