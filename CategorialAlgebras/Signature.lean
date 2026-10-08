import Stemma
import Mathlib.Data.List.Basic

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Many-sorted signatures" =>

Throughout, $`S` is a set of *sorts*. Following the preliminaries of the draft (Section 1),
a *word* on $`S` is a mapping $`\mathbf{s} \colon m \to S` from some natural number
$`m = \{0, \ldots, m-1\}`, written $`\mathbf{s} = (s_j)_{j \in |\mathbf{s}|}`, with *length*
$`|\mathbf{s}| = m`; $`S^{\star}` is the set of words on $`S`, and $`\lambda` is the empty
word. In the Lean, words are lists: a list `w : List S` is the word of length `w.length` whose
$`j`-th letter is `w.get j`, for `j : Fin w.length`, and concatenation of words is `++`.

```lean
universe u v w

namespace CategorialAlgebras
```

:::definition (label := "signature") (central := false) (title := "Many-sorted signature")
An $`S`-*sorted signature* (Definition 1.1 of the draft, labelled `DSignature`) is an
$`S^{\star} \times S`-sorted set
$`\Sigma = (\Sigma_{\mathbf{s}, s})_{(\mathbf{s}, s) \in S^{\star} \times S}` of small sets. An
element $`\sigma \in \Sigma_{\mathbf{s}, s}` is a *formal operation* of *arity* $`\mathbf{s}`,
*sort* (or *coarity*) $`s` and *rank* $`(\mathbf{s}, s)`; when $`\mathbf{s} = \lambda` it is a
*constant* of sort $`s`. A *many-sorted signature* is a pair $`(S, \Sigma)` with $`\Sigma` an
$`S`-sorted signature. The Grothendieck universe $`\boldsymbol{\mathcal{U}}` of small sets of the
draft is a Lean universe `Type v`.

```lean
abbrev Signature (S : Type u) := List S → S → Type v
```
:::

:::definition (label := "signature.arity-product") (central := false) (title := "Products along a word")
Let $`A = (A_s)_{s \in S}` be an $`S`-sorted set and $`\mathbf{s} \in S^{\star}`. Then
$`A_{\mathbf{s}} = \prod_{j \in |\mathbf{s}|} A_{s_j}` is the set of families
$`(a_j)_{j \in |\mathbf{s}|}` with $`a_j \in A_{s_j}`; for $`\mathbf{s} = \lambda` it has a
single element, the empty family.

```lean
abbrev Signature.Arity {S : Type u} (A : S → Type w) (s : List S) : Type w :=
  (j : Fin s.length) → A (s.get j)
```
:::

```lean
end CategorialAlgebras
```
