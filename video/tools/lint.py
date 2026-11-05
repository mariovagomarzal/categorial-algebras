"""Check the script (and, optionally, the scenes) for notation that differs from the paper.

Usage: python -m tools.lint [files...]   (script.md by default)
Exit status 1 if any problem is found.
"""

import re
import sys

from tools.common import ROOT

# (pattern, message, where): where is "all", "voice" (lines starting with "> ") or "visual" (the rest).
RULES = [
    (r"\\otimes", "the operation ⊗ was replaced by σ and τ", "all"),
    (r"(?<![A-Za-z{])[nm]\\mathsf\{Cat", r"write \mathsf{nCatAlg}, \mathsf{mCat}... (sans-serif dimension)", "all"),
    (r"\\overset\{e\}", r"existence equation: \overset{\mathrm e}{=}", "all"),
    (r"\\mathsf\{[nm0-9]?Cat(?:\^\{\\mathrm\{htg\}\}\\mathsf\{)?Alg\}\(\\Sigma\)", r"categories of categorial algebras take \mathbf{\Sigma}", "all"),
    (r"\\mathrm\{T\}_\{\\Lambda\}\(V", r"term contexts are written \mathord{\downarrow}...", "all"),
    (r"\\mathrm\{\{?(ext|gl)\}", "the heterogeneous presentation is marked 'htg' (not 'ext' or 'gl')", "all"),
    (r"(?i)\b(compact|extended) presentation|single-set|globular", "presentations are 'homogeneous' and 'heterogeneous'", "all"),
    (r"hepSig|hepAlg|wEPAlg", "categories are HSig, HAlg and WEPAlg", "all"),
    (r"\bD\s*\\dashv|\\mathrm\{D\}|(?<![A-Za-z\\])T\^\{", "the functors are Ds and Tr", "all"),
    (r"rewrit", "no rewriting in the video", "all"),
    (r"\b(Def|Prop|Cor|Rem|Ex|Lemma)\. \d+\.\d+|arXiv", "no references to the paper on screen", "visual"),
    (r"(?<![\w\[])x\b|(?<!\w)y\b", "variables are read as on screen (v zero, v one), never x or y", "voice"),
    (r"\\mathrm\{(Gd|Uf|Ds|Tr)\}(?![\^_])", "functors always carry their dimensions, e.g. \\mathrm{Gd}^{(n)}", "visual"),
]


def sections(text, name):
    """Yield (line number, line, kind) for the scene part of a script, or every line of other files."""
    in_scenes = not name.endswith(".md")
    for i, line in enumerate(text.splitlines(), 1):
        if name.endswith(".md"):
            if line.startswith("## Part I "):
                in_scenes = True
        if in_scenes:
            yield i, line, "voice" if line.startswith("> ") else "visual"


def main(files):
    problems = 0
    for f in files or ["script.md"]:
        path = ROOT / f
        for i, line, kind in sections(path.read_text(), f):
            for pattern, message, where in RULES:
                if where != "all" and where != kind:
                    continue
                for m in re.finditer(pattern, line):
                    print(f"{f}:{i}: {message}: …{line[max(0, m.start() - 30):m.end() + 30]}…")
                    problems += 1
    print(f"{problems} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
