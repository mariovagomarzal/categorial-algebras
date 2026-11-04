import Stemma
import CategorialAlgebras.Init
import CategorialAlgebras.Tactic
import CategorialAlgebras.Signature
import CategorialAlgebras.PartialAlgebra
import CategorialAlgebras.Evaluation
import CategorialAlgebras.Derivor
import CategorialAlgebras.EpSignature
import CategorialAlgebras.GenEpDerivor
import CategorialAlgebras.GenEpComposition
import CategorialAlgebras.Compact.Category
import CategorialAlgebras.Compact.Functor
import CategorialAlgebras.Compact.Product
import CategorialAlgebras.Compact.Algebra
import CategorialAlgebras.Compact.Specification
import CategorialAlgebras.Compact.Restriction
import CategorialAlgebras.Compact.OmegaAlgebra
import CategorialAlgebras.Compact.Identification
import CategorialAlgebras.Compact.Truncation
import CategorialAlgebras.Compact.Tower
import CategorialAlgebras.Compact.Limit
import CategorialAlgebras.Extended.Category
import CategorialAlgebras.Extended.Functor
import CategorialAlgebras.Extended.Product
import CategorialAlgebras.Extended.Algebra
import CategorialAlgebras.Extended.Specification
import CategorialAlgebras.Extended.Restriction
import CategorialAlgebras.Extended.OmegaAlgebra
import CategorialAlgebras.Extended.Truncation
import CategorialAlgebras.Extended.Limit
import CategorialAlgebras.Extended.Model
import CategorialAlgebras.CategorialEp
import CategorialAlgebras.DerivedEval
import CategorialAlgebras.Graduation
import CategorialAlgebras.Discretization

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "CategorialAlgebras" =>

This library formalizes, in Lean and with Mathlib, the theory of *higher-order categorial
algebras*: many-sorted algebras whose carriers are higher-order categories and whose operations
are higher-order functors. It accompanies the group's draft *Higher-order categorial algebras*
(J. Climent Vidal, E. Cosme Llópez, R. Ruiz Mora and M. Vago Marzal) and checks its results.

# Higher-order categorial algebras

Let $`(S, \Sigma)` be a many-sorted signature and $`n \in \mathbb{N}`. An $`n`-*categorial*
$`\Sigma`-*algebra* interprets every sort $`s \in S` as a strict $`n`-category
$`\mathsf{A}_s` and every operation symbol $`\sigma \in \Sigma_{\mathbf{s}, s}` as an
$`n`-functor $`\sigma^{\mathsf{A}} \colon \mathsf{A}_{\mathbf{s}} \to \mathsf{A}_s`, where
$`\mathsf{A}_{\mathbf{s}}` is the product of the categories of the sorts of $`\mathbf{s}`. For
$`n = 0` these are ordinary many-sorted algebras; for $`n = 1`, algebras in the category of
small categories. Letting $`n` grow without bound gives the $`\omega`-categorial algebras.

Categorial algebras are, at the same time, partial algebras: compositions are defined only on
composable cells. The draft presents the categorial $`\Sigma`-algebras of dimension $`n` as the
models of a specification by QE-equations (implications between existence equations) in a
signature $`\Sigma^{(n)}` that adds the categorial operations to $`\Sigma`. The library writes
down this specification for both presentations; that its models are exactly the categorial
algebras is not formalized yet.

# Two presentations

A higher-order category can be presented in two ways, and the library formalizes both.

- In the *compact* presentation all cells, whatever their dimension, live in a single set; a
  cell is a $`k`-cell when its $`k`-source is itself. An $`n`-category has the dimensions
  $`0, \ldots, n - 1`.
- In the *extended* presentation the $`k`-cells form a separate set $`C_k` for every dimension
  $`k`, with sources, targets, identities and partial compositions between them. An
  $`n`-category has the dimensions $`0, \ldots, n`.

The compact presentation is closer to the classical definition of a category as a set of
arrows; the extended one makes dimensions explicit, and it is the one in which the passage to
dimension $`\omega` is strict.

# Main results

The library claims, and its signers vouch for, the following:

- the definition of a compact $`n`-categorial algebra, {name}`CategorialAlgebras.Compact.CatAlgebra`;
- the definition of an extended $`n`-categorial algebra, {name}`CategorialAlgebras.Extended.CatAlgebra`;
- that the category $`\omega\mathsf{Cat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)` of extended
  $`\omega`-categorial $`\Sigma`-algebras is the projective limit, in $`\mathsf{Cat}`, of the
  categories $`\mathsf{nCat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)` along the truncation functors,
  {name}`CategorialAlgebras.Extended.omegaCatAlg_isLimit`.

In the compact presentation the truncation functors compose only up to canonical isomorphism,
so the corresponding universal property of $`\omega\mathsf{Cat}\mathsf{Alg}(\Sigma)` does not
hold strictly as stated in the draft; how to formulate it is still open.

# Reading order

The chapters follow one another in the order of the table of contents.

1. *Preliminaries*: many-sorted signatures, partial algebras and QE-equations.
2. *The compact presentation*: compact higher-order categories, functors and finite products;
   compact $`n`-categorial algebras and their QE-specification; restriction of dimensions,
   compact $`\omega`-categorial algebras, and truncation.
3. *The extended presentation*: the same sequence for extended categories, ending with
   $`\omega\mathsf{Cat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)` as a projective limit.

The two presentations are developed independently, so the extended one can be read without the
compact one, after the preliminaries.

# The draft and the ported repository

The library follows the group's draft, but it is not a transcription of it: definitions are
refined where the draft is incomplete, and the prose says so where it happens. The documents
refer to the draft by its LaTeX labels (such as `SCompact` or `DManySortedCatAlg`), never by
its numbering, so that they stay valid as the draft changes.

Not every part of the draft is formalized yet. Graduation and unification, discretization,
derivors and their generalizations, the functors in dimension $`\omega`, and the algebraic
square are later lines of work.

The categorial core (compact and extended higher-order categories and their functors) is ported
from the group's repository
[`higher_category_theory`](https://github.com/mariovagomarzal/higher_category_theory) (by Enric
Cosme Llópez, Raúl Ruiz Mora and Mario Vago Marzal, Apache 2.0). There the compact presentation
is called *single-sorted* and the extended one *many-sorted*.
