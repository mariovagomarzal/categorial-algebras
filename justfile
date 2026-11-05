# The recipes of the repository: `just` lists them all.

mod video

[private]
default:
    @just --list --list-submodules

# Build the Lean library.
build:
    lake exe cache get
    lake build

# Build the API documentation and the site, in _site/.
docs:
    scripts/build-docs.sh

# Build the paper, in paper/main.pdf.
paper:
    cd paper && latexmk -pdf main.tex
