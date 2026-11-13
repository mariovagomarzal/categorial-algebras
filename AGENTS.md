# CategorialAlgebras

A Lean 4 formalization, with Mathlib, of the paper in `paper/main.tex`: the
theory of higher-order many-sorted categorial algebras and of the generalized
hep-derivors that relate their presentations and dimensions. See `README.md`
for the layout of the repository.

## Building

- `lake exe cache get` once on a fresh checkout, then `lake build`.
- `scripts/build-docs.sh` builds the API documentation; run it when a change
  touches docstrings.

## The library

- The paper is the mathematical reference, but the library does not refer to
  it: no labels, numbers or names of its chapters, sections or results, in code
  or in docstrings. Docstrings explain the mathematics on their own.
- Works of the bibliography (`paper/references.bib`) may be cited by key, as
  `[Reichel1987]`.
- The paper links its definitions and results to their declarations with
  `\lean{relation}{names}`, where the relation is `equivalent`, `weaker` or
  `stronger` and the names are relative to `CategorialAlgebras`. When a linked
  declaration is renamed, moved or changed, update its mark. A linked
  declaration whose relation is not `equivalent` ends its docstring with a
  paragraph that starts with `**Formally weaker** than the informal statement.`
  or `**Formally stronger** than the informal statement.` and says briefly how
  it differs.
- Everything lives in the namespace `CategorialAlgebras`. Modules follow the
  parts of the theory, under `CategorialAlgebras/`, and `CategorialAlgebras.lean`
  imports all of them.
- Use what Mathlib already has (categories, functors, adjunctions, limits,
  partial values) instead of redefining it.

## Style

- Mathlib's style: a module docstring (`/-! ... -/`) after the imports, `##`
  and `###` module docstrings for sections, and a docstring (`/-- ... -/`) on
  every definition and on every theorem that is a result of the theory.
  Mathematics in docstrings is LaTeX in `$...$`.
- Mathlib's naming conventions: `UpperCamelCase` for types and structures,
  `lowerCamelCase` for definitions, `snake_case` for theorems.
- No new axioms. `sorry` only where a task allows it, and every one listed in
  the report of that task.
