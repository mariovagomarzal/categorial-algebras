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

- **`SDiscretization`**. When this was written the subsection had only its
  title. The draft now defines discretization through the derivor
  `DDiscDerivor` (a generalized ep-derivor), so it can be formalized on top
  of `SGenEpDerivors`.

## Decided: `PUnivPropCatAlg` as a pseudo-limit (2026-10-14)

In the compact presentation the truncation functors compose only up to
canonical isomorphism (`RTmnCatAlgProjSys` is formalized as natural
isomorphisms), so the strict universal property of the draft cannot be stated
faithfully: `T(m,n) ∘ T(n,ω) = T(m,ω)` fails already for the projections. Of
the two routes considered (a pseudo-limit, or deriving it from
`PUnivPropExtCatAlg` through the equivalence between the compact and the
extended presentations), the group chose the pseudo-limit.

The library states it as an equivalence between ωCatAlg(Σ) and the category of
compatible families: algebras `A_n` with isomorphisms
`T(n,n+1)(A_{n+1}) ≅ A_n` between consecutive levels (no coherence condition
is needed for a tower indexed by ℕ), and families of homomorphisms commuting
with them. Fullness and faithfulness are the first part of `CLimitNat`; essential
surjectivity is the limit of a compatible family, built as the union of the
chain of cells. The form with functors, and the second part of `CLimitNat`, follow
formally and are stated only in prose.

## Second scope: generalized ep-derivors (2026-10-14)

The group chose to follow the draft: first `SGenEpDerivors`, then
graduation, unification and discretization as instances of it. The section
`SGenEpDerivors` is formalized and proved in the documents
`Derivor`, `EpSignature`, `GenEpDerivor` and `GenEpComposition`. Decisions:

- The variables of a word are its positions (`Vars κ`), as the draft's
  identification `j ↦ v^s_j` suggests; a family is a valuation.
- Valuations are partial, so `RSubst` needs no hypothesis.
- (GEP2) is asked for every numbering of the variables of each QE-equation,
  which is equivalent to the draft's "after renaming".
- `Dom_d`, `dfd_d` and `tr_d` are defined by well-founded recursion along
  the precedence of the ep-signature, as in the draft (general case kept).
- `LGenEpComp` and the identity law hold up to isomorphisms that send every
  cell to itself, as with `PUnivPropCatAlg`: `Alg_gd` is a pseudofunctor,
  and `epAlg_gd` is Mathlib's `CoGrothendieck` of it.
- The composite uses `Cn`, which ranges over the algebras of a fixed universe;
  the objects of `epSig_gd` record that universe.

Next, in the order of the draft: `SGraduation` (graduation and unification,
the passage between the single-set and the globular presentations), then
`SDiscretization` and the rest of `STruncation`, then dimension ω.

## Third scope: graduation and unification (2026-10-14)

`SGraduation` is formalized in `CategorialEp` and `Graduation`, all proved.
Decisions:

- The compact and extended signatures are ep-signatures whose only domain
  conditions are those of the compositions; their ep-specifications keep the
  whole QE-specification (A0, A1, A3 become redundant), so that
  `PAlg(C) = epAlg(Σ, C)` is immediate (`RCompactEp`, `PExtendedIdent`(1)).
- `PExtendedIdent`(2) (extended categorial algebras are the models of
  `C^ext(n)`) is not formalized: graduation and unification are stated between
  the categories of models, which is what the draft's proofs use. Composing
  with `compact.cat-alg-iso` gives `nCatAlg(Σ) ≃ PAlg(C^ext(n))`.
- `g ∘ u = id` holds as an equality of derivors (`PUnifGrad`), but
  `Uf ∘ Gd ≅ Id` only by isomorphisms that send every cell to itself, as with
  `LGenEpComp`.
- `CGdUfEquiv` and `PGdUfAdj` are one Mathlib adjoint equivalence: unit the
  isomorphism above, counit `θ⁻¹`.

Next: `SDiscretization` and the rest of `STruncation`, then dimension ω.

## Fourth scope: discretization and truncation (2026-10-14)

`SDiscretization`, `STruncationAlg` and the first two results of
`SDiscTrunc` are formalized in `Discretization`, all proved. Decisions:

- The four derivors (`DDiscDerivor`, `DDiscExtDerivor`, `DTruncDerivor` and
  the extended truncation derivor) and their functors are as in the draft.
  The compact and extended discretization derivors are defined, and send
  models to models, for all `m` and `n`, not only `m ≤ n`; for `m ≥ n` they
  keep every dimension of `n`. Truncation needs `m ≤ n`.
- In the extended discretization, for `j ≥ m` the term `v_0` has sort
  `(min(j, m), s)`, equal to `(min(k, m), s)` but not by definition: the
  variable carries that equality, and the proofs transport along it.
- `PTruncDisc` is an equality of functors in the draft. Here
  `T ∘ D ≅ Id` (compact and extended) holds by isomorphisms that send every
  cell to itself, because the cells of the truncation are elements of a
  subset. The draft's argument through `δ ∘ τ = id` is not used.
- `PDiscTruncAdj` is two Mathlib adjunctions, `D ⊣ T` and
  `D^ext ⊣ T^ext`. Their units are the isomorphisms above, not identities.
  Their counits are the draft's: the inclusion of the `m`-cells, and
  `i^(k,m)` at the sorts `(k, s)` with `k > m`.
- The new truncation functors (between categories of models) and the earlier
  ones of `Compact.Truncation` and `Extended.Truncation` (between
  `nCatAlg(Σ)`, used for the limits) are not yet related.

Next:
- `PTruncComp`: truncations and discretizations compose.
- `PCompatGdUf`: they commute with graduation and unification.
- Relating the two truncations.
- Then dimension ω (`SOmegaFunctors`).

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
