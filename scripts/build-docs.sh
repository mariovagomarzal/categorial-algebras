#!/usr/bin/env bash
# Build the API documentation of the library with doc-gen4 and assemble the site in `_site/`:
# the contents of `site/` at the root and the API documentation in `_site/docs/`.
#
# doc-gen4 runs from an auxiliary package in `docbuild/`, so that it is not a dependency of the
# library. It shares `.lake/packages` with the library, and uses the doc-gen4 tag that matches
# `lean-toolchain`.
#
# The pages link every declaration to its source on GitHub, read from the Git remotes of the
# packages. When Git rewrites GitHub URLs to SSH (`url.git@github.com:.insteadOf`), doc-gen4
# cannot read them: run with `DOCGEN_SRC=file` to link to the local files instead.
set -euo pipefail

cd "$(dirname "$0")/.."

toolchain=$(cut -d: -f2 < lean-toolchain)
if [[ ! "$toolchain" =~ ^v4\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
  echo "error: no doc-gen4 tag for the toolchain '$toolchain'" >&2
  exit 1
fi

mkdir -p docbuild/docs
cat > docbuild/lakefile.toml <<EOF
name = "docbuild"
reservoir = false
packagesDir = "../.lake/packages"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$toolchain"

[[require]]
name = "categorialalgebras"
path = "../"
EOF

# doc-gen4 reads the bibliography of the citations `[key]` from `docs/references.bib`.
cp docs/references.bib docbuild/docs/references.bib

cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update categorialalgebras

# The HTML pass of doc-gen4 is skipped while its markers are up to date, and a restored cache
# holds the markers but may hold stale pages of the library: remove both, so that the pages of
# the library are always written again from the current sources.
rm -f .lake/build/doc-data/*.docs_built
rm -rf .lake/build/doc/CategorialAlgebras .lake/build/doc/CategorialAlgebras.html

lake build CategorialAlgebras:docs

cd ..
rm -rf _site
mkdir -p _site
cp -R site/. _site/
cp -R docbuild/.lake/build/doc _site/docs
