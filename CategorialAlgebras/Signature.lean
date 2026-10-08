import Stemma
import Mathlib.Data.List.Basic

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Many-sorted signatures" =>

Throughout, $`S` is a set of *sorts* and $`S^{\star}` the set of words on $`S`. A word
$`\mathbf{s} = (s_0, \ldots, s_{m-1})` has length $`|\mathbf{s}| = m`, and $`\lambda` is the empty
word. In the Lean, words are lists, and the $`j`-th letter of a word `w` is `w.get j`, for
`j : Fin w.length`.

```lean
universe u v w

namespace CategorialAlgebras
```

:::definition (label := "signature") (central := false) (title := "Many-sorted signature")
An $`S`-*sorted signature* is an $`S^{\star} \times S`-sorted set
$`\Sigma = (\Sigma_{\mathbf{s}, s})_{(\mathbf{s}, s) \in S^{\star} \times S}`. An element
$`\sigma \in \Sigma_{\mathbf{s}, s}` is an *operation symbol* of *arity* $`\mathbf{s}` and
*coarity* $`s`; when $`\mathbf{s} = \lambda` it is a *constant* of sort $`s`. A *many-sorted
signature* is a pair $`(S, \Sigma)` with $`\Sigma` an $`S`-sorted signature.

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
