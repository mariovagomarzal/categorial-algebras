# CategorialAlgebras

A Lean 4 formalization, with Mathlib, of the theory of *higher-order categorial
algebras*: many-sorted algebras whose carriers are higher-order categories and
whose operations are higher-order functors. It accompanies the draft
*Higher-order categorial algebras* (J. Climent Vidal, E. Cosme Llópez,
R. Ruiz Mora and M. Vago Marzal) and checks its results.

The overview, the main results and the reading order are in the module
docstring of [`CategorialAlgebras.lean`](CategorialAlgebras.lean). The API
documentation is published at
<https://mariovagomarzal.github.io/categorial-algebras/docs/>.

## Building

```sh
lake exe cache get   # download Mathlib's build
lake build
scripts/build-docs.sh  # the API documentation, in _site/docs/
```

CI builds the library and the documentation on pushes to `main` and on pull
requests to `main`; a push to `main` also publishes `_site/` to GitHub Pages.

## Layout

- `CategorialAlgebras/`: the library. `Signature`, `PartialAlgebra` and
  `Evaluation` are the preliminaries; `Compact/` is the compact (single-set)
  presentation and `Extended/` the extended (globular) one; the rest
  (ep-signatures, generalized ep-derivors, graduation, discretization) relates
  the two.
- `docs/main.tex`, `docs/Biblio.bib`: the draft. The library refers to it by
  its LaTeX labels (such as `SSingleSet` or `DManySortedCatAlg`), never by its
  numbering. `docs/article.tex` is a compact version of it.
- `docs/references.bib`: the works the library's docstrings cite, as `[Rei87]`.
- `docs/notes.md`: the scope agreed, the conventions and what was left out.
- `site/`: the root of the published site; the API documentation goes under
  `docs/` in it.
- `scripts/build-docs.sh`: builds the API documentation with doc-gen4 from an
  auxiliary package in `docbuild/`, and assembles the site in `_site/`.
