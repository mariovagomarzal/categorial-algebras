"""Notation of the paper (../paper/main.tex), as LaTeX strings for MathTex.

Every formula of the video is built from these helpers, so that the notation is
written in one place only; tools/lint.py checks the forbidden forms.
"""

EEQ = r"\overset{\mathrm e}{=}"
GD = r"\mathfrak{gd}"


def sig(name=r"\Sigma"):
    """A many-sorted (hep-)signature in bold: sig() -> \\mathbf{\\Sigma}."""
    return rf"\mathbf{{{name}}}"


def cat(n="n", htg=False, s=None):
    r"""Category of categorial algebras: \mathsf{nCatAlg}(\mathbf{\Sigma}), \omega\mathsf{CatAlg}, ..."""
    s = sig() if s is None else s
    dim = r"\omega" if n == "omega" else n
    head = rf"{dim}\mathsf{{" if n == "omega" else rf"\mathsf{{{dim}"
    body = r"Cat}^{\mathrm{htg}}\mathsf{Alg}" if htg else r"CatAlg}"
    return rf"{head}{body}({s})"


def ext(n="n", htg=False, s=None):
    r"""Categorial extension of a signature: \mathbf{\Sigma}^{(n)} or \mathbf{\Sigma}^{\mathrm{htg}(n)}."""
    s = sig() if s is None else s
    n = r"\omega" if n == "omega" else n
    return rf"{s}^{{\mathrm{{htg}}({n})}}" if htg else rf"{s}^{{({n})}}"


def _dims(*ds):
    return ",".join(r"\omega" if d == "omega" else d for d in ds)


def functor(name, *dims, htg=False, s=None, bold=False):
    r"""Gd, Uf, Ds, Tr with their dimensions: functor("Ds", "n", "m", htg=True) -> \mathrm{Ds}^{\mathrm{htg}(n,m)}.

    `s` adds the signature as a subscript (e.g. sig()); `bold` gives the generalized hep-derivor (\mathbf{Gd}).
    """
    assert name in ("Gd", "Uf", "Ds", "Tr")
    font = r"\mathbf" if bold else r"\mathrm"
    sup = rf"\mathrm{{htg}}({_dims(*dims)})" if htg else rf"({_dims(*dims)})"
    sub = rf"_{{{s}}}" if s else ""
    return rf"{font}{{{name}}}^{{{sup}}}{sub}"


def var(sort="s", i=0):
    """A variable of the paper: v^{s}_{0}."""
    return rf"v^{{{sort}}}_{{{i}}}"


def sc(k="k", sort="s"):
    return rf"\mathrm{{sc}}^{{{k}}}_{{{sort}}}"


def tg(k="k", sort="s"):
    return rf"\mathrm{{tg}}^{{{k}}}_{{{sort}}}"


def comp(k="k", sort="s"):
    return rf"\circ^{{{k}}}_{{{sort}}}"


def gsc(j="j", k="k", sort="s"):
    return rf"\mathrm{{sc}}^{{({j},{k})}}_{{{sort}}}"


def gtg(j="j", k="k", sort="s"):
    return rf"\mathrm{{tg}}^{{({j},{k})}}_{{{sort}}}"


def gid(k="k", j="j", sort="s"):
    return rf"\mathrm{{i}}^{{({k},{j})}}_{{{sort}}}"


def gcomp(j="j", k="k", sort="s"):
    return rf"\circ^{{({j},{k})}}_{{{sort}}}"


def derivor(name=r"\mathbf{c}", generalized=True):
    r"""(\varphi, c, \mathrm{Dom}^{(\varphi,c)}) or (\varphi, c)."""
    return rf"{name}=(\varphi,c,\mathrm{{Dom}}^{{(\varphi,c)}})" if generalized else rf"{name}=(\varphi,c)"


def induced(d=r"\mathbf{c}", arg=None):
    r"""Functor induced by a generalized hep-derivor: \mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{B})."""
    base = rf"{d}^{{\ast}}_{{{GD}}}"
    return rf"{base}({arg})" if arg else base


def domain_condition(k="k", sort="s"):
    r"""\mathrm{def}(\circ^{k}_{s}) = \{\mathrm{sc}^{k}_{s}(v^{s}_{0}) =e \mathrm{tg}^{k}_{s}(v^{s}_{1})\}."""
    return (rf"\mathrm{{def}}({comp(k, sort)})=\{{{sc(k, sort)}({var(sort, 0)})"
            rf"{EEQ}{tg(k, sort)}({var(sort, 1)})\}}")


if __name__ == "__main__":
    for x in [cat(), cat("m", htg=True), cat("omega"), cat("omega", htg=True), ext(), ext(htg=True),
              functor("Gd", "n"), functor("Ds", "n", "m", htg=True), functor("Tr", "n", "omega"),
              functor("Gd", "n", s=sig(), bold=True), domain_condition(), induced(arg=r"\mathbf{B}")]:
        print(x)
