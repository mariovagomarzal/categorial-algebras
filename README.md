# Higher-order many-sorted categorial algebras via generalized hep-derivors

Companion repository of the paper *Higher-order many-sorted categorial algebras
via generalized hep-derivors*, by J. Climent Vidal, E. Cosme Llópez, R. Ruiz Mora
and M. Vago Marzal: its source, its Lean 4 formalization and an explanatory
video.

[Website](https://mariovagomarzal.github.io/categorial-algebras/) |
[arXiv](https://arxiv.org/abs/2611.03553) |
[API documentation](https://mariovagomarzal.github.io/categorial-algebras/docs/)

## Repository

This is the structure of the repository:

- `CategorialAlgebras/`: the Lean library.
- `paper/`: the source of the paper.
- `video/`: the video.
- `site/`: the front page of the website.

## Development

The library is built with Lake, the API documentation with doc-gen4, and the
paper with `latexmk`. These are the commands for each of them:

```sh
lake exe cache get && lake build    # the library
scripts/build-docs.sh               # the API documentation, in _site/docs/
cd paper && latexmk -pdf main.tex   # the paper
```

## License

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE). The
paper and the video are not covered by it: all rights are reserved by their
authors.
