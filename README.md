# CategorialAlgebras

A Lean 4 formalization, with Mathlib, of the theory of *higher-order categorial
algebras*: many-sorted algebras whose carriers are higher-order categories and
whose operations are higher-order functors. It accompanies the paper
*Higher-order many-sorted categorial algebras via generalized hep-derivors*
(J. Climent Vidal, E. Cosme Llópez, R. Ruiz Mora and M. Vago Marzal), whose
source is in [`paper/`](paper/).

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

To compile the paper, run `latexmk -pdf main.tex` in `paper/`.

CI builds the paper, the library and the documentation on pushes to `main` and
on pull requests to `main`; a push to `main` also publishes the site to GitHub
Pages, with the PDF of the paper as `paper.pdf`.

## Layout

- `CategorialAlgebras/`: the library. `Signature`, `PartialAlgebra` and
  `Evaluation` are the preliminaries; `Compact/` is the compact (single-set)
  presentation and `Extended/` the extended (globular) one; the rest
  (ep-signatures, generalized ep-derivors, graduation, discretization) relates
  the two.
- `paper/`: the source of the paper, `main.tex`, with its bibliography,
  `references.bib`, and its BibTeX style. The library refers to the paper by its
  LaTeX labels, never by its numbering, and its docstrings cite the
  bibliography by key, as `[Reichel1987]`; the API documentation lists it.
- `video/`: the video that explains the paper (to come).
- `site/`: the root of the published site; the API documentation goes under
  `docs/` in it.
- `docbuild/`: the auxiliary package that builds the API documentation with
  doc-gen4; its doc-gen4 tag must match `lean-toolchain`.
- `scripts/build-docs.sh`: builds the API documentation from `docbuild/` and
  assembles the site in `_site/`.

## License

The code of the library, of the documentation and of the site is released under
the Apache License 2.0; see [`LICENSE`](LICENSE).

The paper (`paper/`) and the video (`video/`) are not covered by that license:
all rights are reserved by their authors. The BibTeX style
`paper/amsplain-initials.bst` is derived from the AMS style `amsplain.bst` and
keeps the license stated in its header.
