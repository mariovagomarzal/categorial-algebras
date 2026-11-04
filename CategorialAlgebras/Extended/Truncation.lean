import Mathlib.CategoryTheory.Functor.Basic
import CategorialAlgebras.Extended.Restriction
import CategorialAlgebras.Extended.OmegaAlgebra

/-!
# Truncation of globular categorial algebras

Definition `DTmnGlCatAlg` of the draft defines the truncation functors
$\mathrm{Tr}^{\mathrm{gl}(m,n)}_{\Sigma} \colon \mathsf{nCat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma) \to \mathsf{mCat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma)$,
for $m \leq n$, and
$\mathrm{Tr}^{\mathrm{gl}(n,\omega)}_{\Sigma} \colon \omega\mathsf{Cat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma) \to \mathsf{nCat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma)$.
In the globular presentation, truncating at level $m$ keeps the cells of dimension at most
$m$ and forgets the others: it is the restriction of every sort along the inclusion of the
dimensions $\{0, \ldots, m\}$. This file defines these functors and proves that they
form a projective system (Remark `RTmnGlCatAlgProjSys` of the draft).
-/

universe u v w

namespace CategorialAlgebras.Extended

open CategoryTheory

variable {S : Type u} {Sig : Signature.{u, v} S}

/-!
## The inclusions of dimensions

For $m \leq n$ the dimensions $\{0, \ldots, m\}$ of a globular $m$-category are included
in the dimensions $\{0, \ldots, n\}$ of a globular $n$-category, and both in the dimensions
$\mathbb{N}$ of a globular $\omega$-category. These inclusions are strictly monotone.
-/

/-- The inclusion of the dimensions of a globular `m`-category into those of a globular
`n`-category, for `m ≤ n`. -/
abbrev dimIncl {m n : ℕ} (h : m ≤ n) : FinSucc m → FinSucc n :=
  Fin.castLE (Nat.succ_le_succ h)

lemma dimIncl_strictMono {m n : ℕ} (h : m ≤ n) : StrictMono (dimIncl h) :=
  fun _ _ hab => hab

/-- The inclusion of the dimensions of a globular `n`-category into `ℕ`. -/
abbrev dimInclω (n : ℕ) : FinSucc n → ℕ := Fin.val

lemma dimInclω_strictMono (n : ℕ) : StrictMono (dimInclω n) :=
  Fin.val_strictMono

/-!
## Truncation of globular n-categorial algebras
-/

/-!
### Truncation of a globular n-categorial algebra

Let $m \leq n$ and let $\boldsymbol{\mathsf{A}} = (\mathsf{A}, F)$ be a globular
$n$-categorial $\Sigma$-algebra. Its $m$-*truncation* $\mathrm{Tr}^{\mathrm{gl}(m,n)}_{\Sigma}(\boldsymbol{\mathsf{A}})$
is the globular $m$-categorial $\Sigma$-algebra whose carrier of sort $s$ is the globular
$m$-category formed by the cells of $\mathsf{A}_s$ of dimension at most $m$, with the same
sources, targets, identities and compositions, and in which every operation symbol $\sigma$
acts on $k$-cells, for $k \leq m$, as $\sigma^{\boldsymbol{\mathsf{A}}}$ does.

The $m$-truncation of a homomorphism $H = (H_s)_{s \in S}$ keeps, for every sort, the
mappings $H_{s,k}$ for $k \leq m$.
-/

def CatAlgebra.truncate {m n : ℕ} (h : m ≤ n) (A : CatAlgebra.{u, v, w} Sig n) :
    CatAlgebra.{u, v, w} Sig m where
  carrier s k := A s (dimIncl h k)
  str s := Category.restrict (dimIncl_strictMono h) (A s)
  op σ := Functor.restrict (dimIncl_strictMono h) (A.op σ)

def CatAlgebra.Hom.truncate {m n : ℕ} (h : m ≤ n) {A B : CatAlgebra.{u, v, w} Sig n}
    (H : CatAlgebra.Hom A B) : CatAlgebra.Hom (A.truncate h) (B.truncate h) where
  map s := Functor.restrict (dimIncl_strictMono h) (H.map s)
  map_op σ k a := H.map_op σ (dimIncl h k) a

/-- For $m \leq n$, truncation is a functor
$\mathrm{Tr}^{\mathrm{gl}(m,n)}_{\Sigma} \colon \mathsf{nCat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma) \to \mathsf{mCat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma)$:
it preserves identities and composition of homomorphisms, since these are computed
dimensionwise.
-/
def truncation (Sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n) :
    CatAlgebra.{u, v, w} Sig n ⥤ CatAlgebra.{u, v, w} Sig m where
  obj A := A.truncate h
  map H := CatAlgebra.Hom.truncate h H
  map_id _ := rfl
  map_comp _ _ := rfl

/-!
## Truncation of globular ω-categorial algebras
-/

/-!
### Truncation of a globular ω-categorial algebra

Let $n \in \mathbb{N}$ and let $\boldsymbol{\mathsf{A}}$ be a globular $\omega$-categorial
$\Sigma$-algebra. Its $n$-*truncation* $\mathrm{Tr}^{\mathrm{gl}(n,\omega)}_{\Sigma}(\boldsymbol{\mathsf{A}})$
is the globular $n$-categorial $\Sigma$-algebra formed by the cells of dimension at most $n$,
with the same structure and operations; homomorphisms are truncated likewise.
-/

def OmegaCatAlgebra.truncate (n : ℕ) (A : OmegaCatAlgebra.{u, v, w} Sig) :
    CatAlgebra.{u, v, w} Sig n where
  carrier s k := A s (dimInclω n k)
  str s := Category.restrict (dimInclω_strictMono n) (A s)
  op σ := Functor.restrict (dimInclω_strictMono n) (A.op σ)

def OmegaCatAlgebra.Hom.truncate (n : ℕ) {A B : OmegaCatAlgebra.{u, v, w} Sig}
    (H : OmegaCatAlgebra.Hom A B) : CatAlgebra.Hom (A.truncate n) (B.truncate n) where
  map s := Functor.restrict (dimInclω_strictMono n) (H.map s)
  map_op σ k a := H.map_op σ (dimInclω n k) a

/-- For $n \in \mathbb{N}$, truncation is a functor
$\mathrm{Tr}^{\mathrm{gl}(n,\omega)}_{\Sigma} \colon \omega\mathsf{Cat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma) \to \mathsf{nCat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma)$.
-/
def truncationω (Sig : Signature.{u, v} S) (n : ℕ) :
    OmegaCatAlgebra.{u, v, w} Sig ⥤ CatAlgebra.{u, v, w} Sig n where
  obj A := A.truncate n
  map H := OmegaCatAlgebra.Hom.truncate n H
  map_id _ := rfl
  map_comp _ _ := rfl

/-!
## The projective system
-/

/-!
### The globular truncations form a projective system

For all $m \leq n \leq p$,
$\mathrm{Tr}^{\mathrm{gl}(m,n)}_{\Sigma} \circ \mathrm{Tr}^{\mathrm{gl}(n,p)}_{\Sigma} = \mathrm{Tr}^{\mathrm{gl}(m,p)}_{\Sigma}$,
and $\mathrm{Tr}^{\mathrm{gl}(n,n)}_{\Sigma}$ is the identity functor. Hence the categories
$\mathsf{nCat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma)$ and the truncation functors form a
projective system of categories.
-/

theorem truncation_comp (Sig : Signature.{u, v} S) {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    truncation.{u, v, w} Sig hnp ⋙ truncation Sig hmn = truncation Sig (hmn.trans hnp) :=
  rfl

theorem truncation_id (Sig : Signature.{u, v} S) (n : ℕ) :
    truncation.{u, v, w} Sig (le_refl n) = 𝟭 _ :=
  rfl

/-!
*Proof of “The globular truncations form a projective system”.*

Both sides restrict every sort along the same inclusion of dimensions, and every operation of
the restriction is the corresponding operation of the original algebra: the two functors are
equal by definition.
-/

/-- For all $m \leq n$,
$\mathrm{Tr}^{\mathrm{gl}(m,n)}_{\Sigma} \circ \mathrm{Tr}^{\mathrm{gl}(n,\omega)}_{\Sigma} = \mathrm{Tr}^{\mathrm{gl}(m,\omega)}_{\Sigma}$,
so that $(\omega\mathsf{Cat}^{\mathrm{gl}}\mathsf{Alg}(\Sigma), \mathrm{Tr}^{\mathrm{gl}(\cdot,\omega)}_{\Sigma})$
is a cone over the projective system (the paragraph after Remark `RTmnGlCatAlgProjSys` of the draft).
-/
theorem truncationω_comp (Sig : Signature.{u, v} S) {m n : ℕ} (hmn : m ≤ n) :
    truncationω.{u, v, w} Sig n ⋙ truncation Sig hmn = truncationω Sig m :=
  rfl

/-!
*Proof of “Truncations of ω-algebras are compatible”.*

As for Remark `RTmnGlCatAlgProjSys`, both functors are equal by definition.
-/

end CategorialAlgebras.Extended
