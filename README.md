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
- `video/`: the sources of the video, animated with Manim.
- `site/`: the front page of the website.

## Development

The library is built with Lake, the API documentation with doc-gen4, the paper
with `latexmk` and the video with Manim, through the recipes of
[`just`](https://just.systems/):

```sh
just build                 # the library
just docs                  # the API documentation and the site, in _site/
just paper                 # the paper
just video::render         # the video, in video/build/
just                       # every recipe, with what it does
```

The video needs [uv](https://docs.astral.sh/uv/), FFmpeg, LaTeX, Cairo and
Pango; `nix-shell video/shell.nix` provides them. Its narration was generated
with ElevenLabs, and is generated again only when its text changes. Every change
to the video that reaches `main` publishes it as a release, and the website shows
the latest one.

## License

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE). The
paper and the video are not covered by it: all rights are reserved by their
authors.
