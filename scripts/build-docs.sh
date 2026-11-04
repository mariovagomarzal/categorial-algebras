#!/usr/bin/env bash
# Build the API documentation of the library with doc-gen4 and assemble the site in `_site/`:
# the contents of `site/` at the root and the API documentation in `_site/docs/`.
#
# doc-gen4 runs from the auxiliary package `docbuild/`, so that it is not a dependency of the
# library. It shares `.lake/packages` with the library. Its manifest pins doc-gen4 and its
# dependencies; when `lean-toolchain` changes, set the doc-gen4 tag in `docbuild/lakefile.toml`
# to the new toolchain and run `lake update` in `docbuild/`.
#
# The pages link every declaration to its source on GitHub. doc-gen4 finds these links by running
# `git` in every package, from jobs that block Lake's workers; on a graph as large as Mathlib's,
# the GitHub runners then fail to start these processes (errno 12, ENOMEM), whatever the memory
# and the number of threads: https://github.com/leanprover/doc-gen4/issues/434. So doc-gen4
# links to the local files (`DOCGEN_SRC=file`), and this script rewrites the links to GitHub: the
# packages at the revisions of `lake-manifest.json`, and the library at the current commit. Once
# that issue is fixed, drop `DOCGEN_SRC=file` and the rewriting.
set -euo pipefail

cd "$(dirname "$0")/.."

toolchain=$(cut -d: -f2 < lean-toolchain)
if [[ ! "$toolchain" =~ ^v4\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
  echo "error: no doc-gen4 tag for the toolchain '$toolchain'" >&2
  exit 1
fi

docgen=$(sed -n 's/^rev = "\(.*\)"$/\1/p' docbuild/lakefile.toml)
if [[ "$docgen" != "$toolchain" ]]; then
  echo "error: docbuild/lakefile.toml asks for doc-gen4 $docgen, but lean-toolchain is $toolchain" >&2
  exit 1
fi

mkdir -p docbuild/docs
# doc-gen4 reads the bibliography of the citations `[key]` from `docs/references.bib`.
cp docs/references.bib docbuild/docs/references.bib

cd docbuild
# Bring the library's dependencies in the manifest of `docbuild/` to those of the library, so
# that building here never checks out other revisions in the shared `.lake/packages`.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update categorialalgebras

# The HTML pass of doc-gen4 is skipped while its markers are up to date, and a restored cache
# holds the markers but may hold stale pages of the library: remove both, so that the pages of
# the library are always written again from the current sources.
rm -f .lake/build/doc-data/*.docs_built
rm -rf .lake/build/doc/CategorialAlgebras .lake/build/doc/CategorialAlgebras.html

DOCGEN_SRC=file lake build CategorialAlgebras:docs

cd ..
rm -rf _site
mkdir -p _site
cp -R site/. _site/
cp -R docbuild/.lake/build/doc _site/docs

python3 - <<'PY'
import json, os, pathlib, re, subprocess

def https(url):
    url = re.sub(r'^git@([^:]+):', r'https://\1/', url)
    return url[:-len('.git')] if url.endswith('.git') else url

def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

links = []
for pkg in json.load(open('lake-manifest.json'))['packages']:
    local = os.path.realpath(os.path.join('.lake/packages', pkg['name']))
    remote = f"{https(pkg['url'])}/blob/{pkg['rev']}/"
    if pkg.get('subDir'):
        remote += pkg['subDir'].strip('/') + '/'
    links.append((f'file://{local}/', remote))
# The library last, since the packages live inside it.
links.append((f"file://{os.path.realpath('.')}/",
              f"{https(git('remote', 'get-url', 'origin'))}/blob/{git('rev-parse', 'HEAD')}/"))

pattern = re.compile('|'.join(re.escape(local) for local, _ in links))
remote_of = dict(links)
left = 0
for page in pathlib.Path('_site/docs').rglob('*.html'):
    text = page.read_text(encoding='utf-8')
    new = pattern.sub(lambda m: remote_of[m.group(0)], text)
    if new != text:
        page.write_text(new, encoding='utf-8')
    left += new.count(f"file://{os.path.realpath('.')}")
if left:
    raise SystemExit(f'error: {left} links to local files are left in the site')
PY
