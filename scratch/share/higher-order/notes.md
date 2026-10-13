# Higher-order categorial algebras: notes for the library

`main.tex` is the group's draft (Climent Vidal, Cosme Llópez, Ruiz Mora, Vago
Marzal), with its bibliography in `Biblio.bib`. The library checks its results
against it. Refer to the draft by its LaTeX labels (such as
`DManySortedCatAlg` or `SCompact`), never by its numbers, so that new text in
`main.tex` changes nothing here.

These notes keep what the source plans of stemma 0.4 recorded and the library
does not: the scope agreed, the conventions, and why some parts of the draft
were left out. The plans themselves (`*.toml`) are in the history.

## Reading the draft

`SIntroduction` holds the prerequisites, notation and terminology; the
sections after it are the body. Appendices A (`S0C`, many-sorted sets and
algebras) and B (`S0D`, many-sorted partial algebras) are reference material
for completing definitions the body leaves out. Where they overlap the body
(`SDerivors` and Appendix A on derivors, `DQEEq` and Appendix B on
QE-equations), the body prevails. Definitions are refined where the draft is
wrong or incomplete, and the library's prose says so.

## First scope (agreed 2026-10-08)

In order:

1. `SPreliminaries`: words, many-sorted sets, signatures, partial algebras and
   QE-equations.
2. `SCompact`: compact n-categories, many-sorted compact n-categorial
   algebras, their category and their QE specification.
3. `SExtended`: the extended presentation and its algebras.
4. `STruncation`: truncation and discretization of algebras.
5. `SLimitCompact`, `SLimitExtended`: ωCatAlg as a projective limit.

Out of this first scope, as a separate line of work: `SDerivors`,
`SGenDerivors`, `SEpDerivors`, `SGenEpDerivors` (Hall algebras, derivors),
`SGraduation` (graduation and unification) and `SAlgSquare` (algebraic
squares).

## Reuse

The categorial core is ported from the group's repository
<https://github.com/mariovagomarzal/higher_category_theory> (Apache 2.0;
authors Cosme Llópez, Ruiz Mora, Vago Marzal): its single-sorted presentation
is the compact one, its many-sorted presentation the extended one.

From Mathlib: partial functions (`Part`, `PFun`) and category theory
(`CategoryTheory.Category`, functors, limits). Mathlib has no many-sorted
universal algebra and no strict n-categories, so signatures and algebras are
the library's own.

## Conventions

- A signature on sorts `S` is `List S → S → Type`.
- An n-category is indexed by `Fin n` in the compact presentation and by
  `Fin (n + 1)` in the extended one, as in the ported repository.
- Composition is a partial operation `C → C →. C` whose domain is exactly the
  composable pairs.

## Open: what the library could not do

- **`PUnivPropCatAlg`** (universal property of ωCatAlg, compact
  presentation). In the compact presentation the truncation functors compose
  only up to canonical isomorphism (`RTmnCatAlgProjSys` is formalized as
  natural isomorphisms), so the strict universal property of the draft cannot
  be stated faithfully. It needs a decision: a pseudo-limit version (families
  coherent up to isomorphism), or deriving it from `PUnivPropExtCatAlg`
  through the equivalence between the compact and the extended presentations.
- **`SDiscretization`**. The subsection has only its title: there is no
  definition of discretization to formalize, and nothing else in the draft
  uses it.

## Left out on 2026-10-08

Why each part of the derivors line was left out at that date. The draft has
changed since (see `scratch/ruizmoraraul/canvis.md`), so some of these reasons
may no longer hold.

- `SDerivors`: out of the first scope, a separate line of work.
- `SGenDerivors`: a placeholder in the draft (a definition taken from
  elsewhere, marked to be replaced).
- `SEpDerivors`: a draft definition marked by the authors as possibly
  incorrect.
- `SGenEpDerivors`: the section had only its title.
- `DefAlgSquare`: algebraic squares, out of the first scope.
