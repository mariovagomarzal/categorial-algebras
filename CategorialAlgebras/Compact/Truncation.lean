import Stemma
import Mathlib.CategoryTheory.NatIso
import CategorialAlgebras.Compact.OmegaAlgebra

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Truncation of compact categorial algebras" =>

Definition 10.1 of the draft (labelled `DTmnCatAlg`) defines the truncation
functors $`T^{(m,n)}_{\Sigma} \colon \mathsf{nCatAlg}(\Sigma) \to \mathsf{mCatAlg}(\Sigma)`, for
$`m \leq n`, and $`T^{(n,\omega)}_{\Sigma} \colon \omega\mathsf{CatAlg}(\Sigma) \to \mathsf{nCatAlg}(\Sigma)`.
In the compact presentation, truncating at level $`m` keeps the cells of dimension at most
$`m`, that is, the cells that are $`k`-cells for every $`k \geq m`, with the structure of the
dimensions below $`m`.

Unlike the extended truncation functors, these functors compose only up to a canonical
isomorphism: the $`m`-truncation of the $`n`-truncation of $`\boldsymbol{\mathsf{A}}` has as
cells the $`m`-cells *of the set of* $`n`-cells of $`\boldsymbol{\mathsf{A}}`, which are the
$`m`-cells of $`\boldsymbol{\mathsf{A}}` with a proof that they are $`n`-cells, not the
$`m`-cells of $`\boldsymbol{\mathsf{A}}` themselves. Remark 11.1 is therefore stated below as a
natural isomorphism.

```lean
universe u v w

namespace CategorialAlgebras.Compact

open CategoryTheory

variable {S : Type u} {Sig : Signature.{u, v} S}
```

# The forgotten dimensions

```lean
/-- The dimensions of a compact `n`-category forgotten by truncating at `m`. -/
def upper (m n : ℕ) : Set (Fin n) := {k | m ≤ k.val}

/-- The dimensions of a compact `ω`-category forgotten by truncating at `n`. -/
def upperω (n : ℕ) : Set ℕ := {k | n ≤ k}

lemma castLE_strictMono {m n : ℕ} (h : m ≤ n) : StrictMono (Fin.castLE h) :=
  fun _ _ hab => hab

lemma upper_spec {m n : ℕ} (h : m ≤ n) : ∀ j : Fin m, ∀ u ∈ upper m n, Fin.castLE h j < u :=
  fun j u hu => Nat.lt_of_lt_of_le j.isLt hu

lemma upperω_spec (n : ℕ) : ∀ j : Fin n, ∀ u ∈ upperω n, (j : ℕ) < u :=
  fun j u hu => Nat.lt_of_lt_of_le j.isLt hu
```

# Truncation of compact n-categorial algebras

:::definition (label := "compact.truncate") (central := false) (title := "Truncation of a compact n-categorial algebra")
Let $`m \leq n` and let $`\boldsymbol{\mathsf{A}}` be a compact $`n`-categorial
$`\Sigma`-algebra. Its $`m`-*truncation* $`T^{(m,n)}_{\Sigma}(\boldsymbol{\mathsf{A}})` is the
compact $`m`-categorial $`\Sigma`-algebra whose carrier of sort $`s` is the restriction of
$`\mathsf{A}_s` to its cells that are $`k`-cells for every $`k \in n` with $`k \geq m`, with the
sources, targets and compositions of dimension $`k < m`, and in which every operation acts as in
$`\boldsymbol{\mathsf{A}}` (it preserves these cells, being a compact functor). The
$`m`-truncation of a homomorphism is its restriction to these cells.

```lean
def CatAlgebra.truncate {m n : ℕ} (h : m ≤ n) (A : CatAlgebra.{u, v, w} Sig n) :
    CatAlgebra.{u, v, w} Sig m where
  carrier s := Restr (upper m n) (A s)
  str s := Category.restrict (castLE_strictMono h) (upper_spec h) (A s)
  op σ := Functor.restrictPi (castLE_strictMono h) (upper_spec h) (A.op σ)

def CatAlgebra.Hom.truncate {m n : ℕ} (h : m ≤ n) {A B : CatAlgebra.{u, v, w} Sig n}
    (H : CatAlgebra.Hom A B) : CatAlgebra.Hom (A.truncate h) (B.truncate h) where
  map s := Functor.restrict (castLE_strictMono h) (upper_spec h) (H.map s)
  map_op σ a := Subtype.ext (H.map_op σ (fun l => (a l).1))
```
:::

:::definition (label := "compact.truncation-functor") (central := false) (title := "The truncation functor T(m,n)")
For $`m \leq n`, truncation is a functor
$`T^{(m,n)}_{\Sigma} \colon \mathsf{nCatAlg}(\Sigma) \to \mathsf{mCatAlg}(\Sigma)`.

```lean
def truncation (Sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n) :
    CatAlgebra.{u, v, w} Sig n ⥤ CatAlgebra.{u, v, w} Sig m where
  obj A := A.truncate h
  map H := CatAlgebra.Hom.truncate h H
  map_id _ := rfl
  map_comp _ _ := rfl
```
:::

# Truncation of compact ω-categorial algebras

:::definition (label := "compact.truncate-omega") (central := false) (title := "Truncation of a compact ω-categorial algebra")
Let $`n \in \mathbb{N}` and let $`\boldsymbol{\mathsf{A}}` be a compact $`\omega`-categorial
$`\Sigma`-algebra. Its $`n`-*truncation* $`T^{(n,\omega)}_{\Sigma}(\boldsymbol{\mathsf{A}})` is
the compact $`n`-categorial $`\Sigma`-algebra formed by the cells that are $`k`-cells for every
$`k \geq n`, with the structure of the dimensions $`k < n`; homomorphisms are restricted
likewise. This is a functor
$`T^{(n,\omega)}_{\Sigma} \colon \omega\mathsf{CatAlg}(\Sigma) \to \mathsf{nCatAlg}(\Sigma)`.

```lean
def OmegaCatAlgebra.truncate (n : ℕ) (A : OmegaCatAlgebra.{u, v, w} Sig) :
    CatAlgebra.{u, v, w} Sig n where
  carrier s := Restr (upperω n) (A s)
  str s := Category.restrict Fin.val_strictMono (upperω_spec n) (A s)
  op σ := Functor.restrictPi Fin.val_strictMono (upperω_spec n) (A.op σ)

def OmegaCatAlgebra.Hom.truncate (n : ℕ) {A B : OmegaCatAlgebra.{u, v, w} Sig}
    (H : OmegaCatAlgebra.Hom A B) : CatAlgebra.Hom (A.truncate n) (B.truncate n) where
  map s := Functor.restrict Fin.val_strictMono (upperω_spec n) (H.map s)
  map_op σ a := Subtype.ext (H.map_op σ (fun l => (a l).1))

def truncationω (Sig : Signature.{u, v} S) (n : ℕ) :
    OmegaCatAlgebra.{u, v, w} Sig ⥤ CatAlgebra.{u, v, w} Sig n where
  obj A := A.truncate n
  map H := OmegaCatAlgebra.Hom.truncate n H
  map_id _ := rfl
  map_comp _ _ := rfl
```
:::

# The projective system, up to isomorphism

```lean
namespace CatAlgebra

variable {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p)

/-- The cells of the `m`-truncation of the `n`-truncation are the cells of the
`m`-truncation. -/
def truncTruncToTrunc (A : CatAlgebra.{u, v, w} Sig p) :
    Hom ((A.truncate hnp).truncate hmn) (A.truncate (hmn.trans hnp)) where
  map s :=
    { map := fun x => ⟨x.1.1, fun u hu => by
        by_cases hn : n ≤ u.val
        · exact x.1.2 u hn
        · exact congrArg Subtype.val (x.2 ⟨u.val, by omega⟩ hu)⟩
      map_sc_eq_sc_map := fun _ _ => rfl
      map_tg_eq_tg_map := fun _ _ => rfl
      map_comp_eq_comp_map := fun _ => rfl }
  map_op _ _ := rfl

/-- The inverse of `truncTruncToTrunc`. -/
def truncToTruncTrunc (A : CatAlgebra.{u, v, w} Sig p) :
    Hom (A.truncate (hmn.trans hnp)) ((A.truncate hnp).truncate hmn) where
  map s :=
    { map := fun y => ⟨⟨y.1, fun u hu => y.2 u (le_trans hmn hu)⟩,
        fun u hu => Subtype.ext (y.2 (Fin.castLE hnp u) hu)⟩
      map_sc_eq_sc_map := fun _ _ => rfl
      map_tg_eq_tg_map := fun _ _ => rfl
      map_comp_eq_comp_map := fun _ => rfl }
  map_op _ _ := rfl

/-- The `n`-truncation of a compact `n`-categorial algebra is the algebra itself, up to the
inclusion of its cells. -/
def truncSelfToSelf (A : CatAlgebra.{u, v, w} Sig n) : Hom (A.truncate le_rfl) A where
  map s :=
    { map := fun x => x.1
      map_sc_eq_sc_map := fun _ _ => rfl
      map_tg_eq_tg_map := fun _ _ => rfl
      map_comp_eq_comp_map := fun _ => rfl }
  map_op _ _ := rfl

def selfToTruncSelf (A : CatAlgebra.{u, v, w} Sig n) : Hom A (A.truncate le_rfl) where
  map s :=
    { map := fun f => ⟨f, fun u hu => absurd u.isLt (Nat.not_lt.mpr hu)⟩
      map_sc_eq_sc_map := fun _ _ => rfl
      map_tg_eq_tg_map := fun _ _ => rfl
      map_comp_eq_comp_map := fun _ => rfl }
  map_op _ _ := rfl

end CatAlgebra

namespace OmegaCatAlgebra

variable {m n : ℕ} (hmn : m ≤ n)

def truncTruncToTrunc (A : OmegaCatAlgebra.{u, v, w} Sig) :
    CatAlgebra.Hom ((A.truncate n).truncate hmn) (A.truncate m) where
  map s :=
    { map := fun x => ⟨x.1.1, fun u hu => by
        by_cases hn : n ≤ u
        · exact x.1.2 u hn
        · exact congrArg Subtype.val (x.2 ⟨u, by omega⟩ hu)⟩
      map_sc_eq_sc_map := fun _ _ => rfl
      map_tg_eq_tg_map := fun _ _ => rfl
      map_comp_eq_comp_map := fun _ => rfl }
  map_op _ _ := rfl

def truncToTruncTrunc (A : OmegaCatAlgebra.{u, v, w} Sig) :
    CatAlgebra.Hom (A.truncate m) ((A.truncate n).truncate hmn) where
  map s :=
    { map := fun y => ⟨⟨y.1, fun u hu => y.2 u (le_trans hmn hu)⟩,
        fun u hu => Subtype.ext (y.2 u hu)⟩
      map_sc_eq_sc_map := fun _ _ => rfl
      map_tg_eq_tg_map := fun _ _ => rfl
      map_comp_eq_comp_map := fun _ => rfl }
  map_op _ _ := rfl

end OmegaCatAlgebra
```

:::proposition (label := "compact.truncation-proj-system") (central := false) (title := "Remark 11.1")
For all $`m \leq n \leq p`, the functors $`T^{(m,n)}_{\Sigma} \circ T^{(n,p)}_{\Sigma}` and
$`T^{(m,p)}_{\Sigma}` are naturally isomorphic, by the isomorphism that sends a cell to itself,
and $`T^{(n,n)}_{\Sigma}` is naturally isomorphic to the identity functor. Likewise
$`T^{(m,n)}_{\Sigma} \circ T^{(n,\omega)}_{\Sigma}` is naturally isomorphic to
$`T^{(m,\omega)}_{\Sigma}`.

Remark 11.1 of the draft states the equations
$`T^{(m,n)}_{\Sigma} \circ T^{(n,p)}_{\Sigma} = T^{(m,p)}_{\Sigma}` on the nose: in set theory,
where the cells of a truncation are a subset of the cells, they hold; in the formalization, a
cell of the truncation is a cell together with a proof that it has the right dimension, and the
two sides only agree up to the canonical isomorphism. In the extended presentation the
equations hold on the nose (Remark 12.1).

```lean
def truncation_comp_iso (Sig : Signature.{u, v} S) {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    truncation.{u, v, w} Sig hnp ⋙ truncation Sig hmn ≅ truncation Sig (hmn.trans hnp) :=
  NatIso.ofComponents
    (fun A =>
      { hom := CatAlgebra.truncTruncToTrunc hmn hnp A
        inv := CatAlgebra.truncToTruncTrunc hmn hnp A
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

def truncation_id_iso (Sig : Signature.{u, v} S) (n : ℕ) :
    truncation.{u, v, w} Sig (le_refl n) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun A =>
      { hom := CatAlgebra.truncSelfToSelf A
        inv := CatAlgebra.selfToTruncSelf A
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

def truncationω_comp_iso (Sig : Signature.{u, v} S) {m n : ℕ} (hmn : m ≤ n) :
    truncationω.{u, v, w} Sig n ⋙ truncation Sig hmn ≅ truncationω Sig m :=
  NatIso.ofComponents
    (fun A =>
      { hom := OmegaCatAlgebra.truncTruncToTrunc hmn A
        inv := OmegaCatAlgebra.truncToTruncTrunc hmn A
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)
```
:::

:::proof (of := "compact.truncation-proj-system")
A cell of $`T^{(m,n)}_{\Sigma}(T^{(n,p)}_{\Sigma}(\boldsymbol{\mathsf{A}}))` is a cell $`f` of
$`\boldsymbol{\mathsf{A}}` that is a $`k`-cell for every $`k \geq n` and, among the dimensions
below $`n`, for every $`k \geq m`: that is, a $`k`-cell for every $`k \geq m`, which is what a
cell of $`T^{(m,p)}_{\Sigma}(\boldsymbol{\mathsf{A}})` is. Conversely, a $`k`-cell for every
$`k \geq m` is in particular a $`k`-cell for every $`k \geq n`. Both mappings send a cell to
itself, so they preserve the structure and the operations, are mutually inverse, and are
natural. For $`T^{(n,n)}_{\Sigma}` there is no dimension $`k \geq n` in $`n`, so every cell is
kept.
:::

```lean
end CategorialAlgebras.Compact
```
