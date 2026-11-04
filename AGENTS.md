# CategorialAlgebras

A Lean 4 + Mathlib library; see `README.md` for its layout.

- Build with `lake build`; run `lake exe cache get` first on a fresh checkout.
- Files follow Mathlib's style: a module docstring (`/-! ... -/`) after the
  imports, `##`/`###` module docstrings for sections, and docstrings
  (`/-- ... -/`) on declarations. Mathematics in docstrings is LaTeX in `$...$`.
- Refer to the paper (`paper/main.tex`) by its LaTeX labels, never by its
  numbering, and cite its bibliography (`paper/references.bib`) by key, as
  `[Reichel1987]`.
