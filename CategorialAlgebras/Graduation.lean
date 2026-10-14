import Stemma
import CategorialAlgebras.CategorialEp
import CategorialAlgebras.GenEpComposition

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Graduation and unification" =>

A compact $`n`-categorial algebra keeps all its cells in a single set for every sort, whatever
their dimension; an extended one keeps the $`k`-cells in a sort of their own, for every
$`k \leq n`. Graduation distributes the cells of a compact algebra into sorts according to their
dimension, and unification keeps only the $`n`-cells of an extended algebra, in which every
$`k`-cell has been replaced by its identity $`n`-cell (Section `SGraduation` of the draft). Both
are induced by generalized ep-derivors between the ep-specifications of Document
`compact.ep-specification` and `extended.ep-specification`, and they are mutually quasi-inverse
equivalences of categories.

Throughout, $`\Sigma` is an $`S`-sorted signature and $`n \in \mathbb{N}`; the dimensions of the
compact presentation are the elements of $`n`, `Fin n` in the Lean, and those of the extended
presentation the elements of $`n + 1`, `Fin (n + 1)`.

```lean
universe u v w

namespace CategorialAlgebras

open Signature Term CategoryTheory

variable {S : Type u} (Sig : Signature.{u, v} S) (n : ℕ)

/-- The dimension `j ∈ n` of a `(j,k)`-source, for `j < k` in `n + 1`. -/
def lowDim {n : ℕ} {j k : Fin (n + 1)} (h : j < k) : Fin n :=
  ⟨j.val, by have := Fin.lt_def.mp h; have := k.isLt; omega⟩
```

# Graduation

Graduating a compact $`n`-categorial algebra $`\mathbf{B}` gives the extended algebra whose cells
of sort $`(k, s)`, for $`k \in n`, are the $`k`-cells of sort $`s` of $`\mathbf{B}`, the cells $`x`
with $`\mathrm{sc}^{k}_{s}(x) = x`, and whose cells of sort $`(n, s)` are all the cells of sort
$`s`. The $`(j,k)`-source and the $`(j,k)`-target of a $`k`-cell are its $`j`-source and its
$`j`-target, the $`(k,j)`-identity of a $`j`-cell is the cell itself, the $`j`-composition of two
$`k`-cells is their $`j`-composition, and $`\sigma_k` acts on $`k`-cells as $`\sigma`.

:::definition (label := "graduation-derivor") (central := false) (title := "The graduation derivor")
The *graduation derivor* $`\mathbf{g}^{(n)} = (\varphi, D, d)` is the generalized ep-derivor from
$`\mathbf{\Sigma}^{\mathrm{ext}(n)}` to $`\mathbf{\Sigma}^{(n)}` with $`\varphi(k, s) = s`,
$`D_{(k,s)} = \{\mathrm{sc}^{k}_{s}(v) \overset{\mathrm{e}}{=} v\}` for $`k \in n` and
$`D_{(n,s)} = \varnothing`, and, for $`j < k`,
$`d(\sigma_k) = \sigma((v_p)_p)`, $`d(\mathrm{sc}^{(j,k)}_{s}) = \mathrm{sc}^{j}_{s}(v_0)`,
$`d(\mathrm{tg}^{(j,k)}_{s}) = \mathrm{tg}^{j}_{s}(v_0)`, $`d(\mathrm{i}^{(k,j)}_{s}) = v_0` and
$`d(\circ^{(j,k)}_{s}) = v_0 \circ^{j}_{s} v_1`.

```lean
/-- The domains of the graduation derivor. -/
def gradDom (t : Fin (n + 1) × S) :
    Set (EEq (Compact.CompactSignature Sig (Fin n)) (Vars fun _ : Unit => t.2)) :=
  if hk : t.1.val < n then
    {EEq.mk' (app₁ (.sc ⟨t.1.val, hk⟩ t.2) (.var ⟨(), rfl⟩)) (.var ⟨(), rfl⟩)}
  else ∅

/-- The terms of the graduation derivor. -/
def gradOp : ∀ {ws : List (Fin (n + 1) × S)} {t : Fin (n + 1) × S},
    Extended.ExtendedSignature Sig (Fin (n + 1)) ws t →
    Term (Compact.CompactSignature Sig (Fin n)) (Vars (Prod.snd ∘ ws.get)) t.2
  | _, _, .op _ σ => .app (.op σ) fun p => .var ⟨Fin.cast (by simp) p, by simp⟩
  | _, _, .sc h s => app₁ (.sc (lowDim h) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .tg h s => app₁ (.tg (lowDim h) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .idm _ _ => .var ⟨⟨0, by simp⟩, rfl⟩
  | _, _, .comp h s =>
      app₂ (.comp (lowDim h) s) (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩)

/-- The graduation derivor `𝐠⁽ⁿ⁾`. -/
def grad : GenEpDerivor (extendedEpSig Sig (Fin (n + 1))) (compactEpSig Sig (Fin n)) where
  sortMap := Prod.snd
  sortDom := gradDom Sig n
  op := gradOp Sig n
```
:::

:::proposition (label := "graduation-models") (central := false) (title := "Graduation sends models to models")
$`(\mathbf{g}^{(n)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})` to models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})`.

```lean
theorem grad_sendsModels :
    (grad Sig n).SendsModels.{u, max u v, u, max u v, w}
      (Extended.extendedSpec Sig (Fin (n + 1))) (Compact.compactSpec Sig (Fin n)) := by
  sorry
```
:::

:::definition (label := "graduation-functor") (central := false) (title := "The graduation functor")
The *graduation functor* $`\mathrm{Gd}^{(n)}` is the birestriction of
$`(\mathbf{g}^{(n)})^{\ast}_{\mathfrak{gd}}` to the categories of models, from
$`\mathsf{PAlg}(\mathcal{C}^{\Sigma^{(n)}})` to $`\mathsf{PAlg}(\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})`.

```lean
/-- The graduation functor `Gd⁽ⁿ⁾`. -/
noncomputable def gradFunctor :
    EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin n)) ⥤
      EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (n + 1))) :=
  (grad Sig n).restrict (grad_sendsModels Sig n)
```
:::

# Unification

Unifying an extended $`n`-categorial algebra $`\mathbf{A}` keeps only its $`n`-cells: the
$`k`-source of an $`n`-cell is the $`(n,k)`-identity of its $`(k,n)`-source, the $`k`-composition
is the $`k`-composition of $`n`-cells, and $`\sigma` acts as $`\sigma_n`.

:::definition (label := "unification-derivor") (central := false) (title := "The unification derivor")
The *unification derivor* $`\mathbf{u}^{(n)} = (\varphi, D, d)` is the generalized ep-derivor from
$`\mathbf{\Sigma}^{(n)}` to $`\mathbf{\Sigma}^{\mathrm{ext}(n)}` with $`\varphi(s) = (n, s)`,
$`D_s = \varnothing`, and, for $`k \in n`, $`d(\sigma) = \sigma_n((v_p)_p)`,
$`d(\mathrm{sc}^{k}_{s}) = \mathrm{i}^{(n,k)}_{s}(\mathrm{sc}^{(k,n)}_{s}(v_0))`,
$`d(\mathrm{tg}^{k}_{s}) = \mathrm{i}^{(n,k)}_{s}(\mathrm{tg}^{(k,n)}_{s}(v_0))` and
$`d(\circ^{k}_{s}) = v_0 \circ^{(k,n)}_{s} v_1`.

```lean
/-- The terms of the unification derivor. -/
def unifOp : ∀ {ws : List S} {s : S}, Compact.CompactSignature Sig (Fin n) ws s →
    Term (Extended.ExtendedSignature Sig (Fin (n + 1)))
      (Vars ((fun s => (Fin.last n, s)) ∘ ws.get)) (Fin.last n, s)
  | _, _, .op σ => .app (.op (Fin.last n) σ) fun q => .var ⟨Fin.cast (by simp) q, by simp⟩
  | _, _, .sc k s => app₁ (.idm (Fin.castSucc_lt_last k) s)
      (app₁ (.sc (Fin.castSucc_lt_last k) s) (.var ⟨⟨0, by simp⟩, rfl⟩))
  | _, _, .tg k s => app₁ (.idm (Fin.castSucc_lt_last k) s)
      (app₁ (.tg (Fin.castSucc_lt_last k) s) (.var ⟨⟨0, by simp⟩, rfl⟩))
  | _, _, .comp k s => app₂ (.comp (Fin.castSucc_lt_last k) s)
      (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩)

/-- The unification derivor `𝐮⁽ⁿ⁾`. -/
def unif : GenEpDerivor (compactEpSig Sig (Fin n)) (extendedEpSig Sig (Fin (n + 1))) where
  sortMap s := (Fin.last n, s)
  sortDom _ := ∅
  op := unifOp Sig n
```
:::

:::proposition (label := "unification-models") (central := false) (title := "Unification sends models to models")
$`(\mathbf{u}^{(n)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})` to models of
$`(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})`.

```lean
theorem unif_sendsModels :
    (unif Sig n).SendsModels.{u, max u v, u, max u v, w}
      (Compact.compactSpec Sig (Fin n)) (Extended.extendedSpec Sig (Fin (n + 1))) := by
  sorry
```
:::

:::definition (label := "unification-functor") (central := false) (title := "The unification functor")
The *unification functor* $`\mathrm{Uf}^{(n)}` is the birestriction of
$`(\mathbf{u}^{(n)})^{\ast}_{\mathfrak{gd}}` to the categories of models.

```lean
/-- The unification functor `Uf⁽ⁿ⁾`. -/
noncomputable def unifFunctor :
    EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (n + 1))) ⥤
      EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin n)) :=
  (unif Sig n).restrict (unif_sendsModels Sig n)
```
:::

```lean
end CategorialAlgebras
```
