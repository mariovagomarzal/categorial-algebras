# Higher-order many-sorted categorial algebras via generalized hep-derivors — Manim video script

**Based on:** *Higher-order many-sorted categorial algebras via generalized hep-derivors*, J. Climent Vidal, E. Cosme Llópez, R. Ruiz Mora and M. Vago Marzal (`../paper/main.tex`).
**Audience:** viewers who know what a category and a functor are.
**Voice-over language:** English (ElevenLabs, voice George).

---

## Notation (as in the paper)

Every formula on screen uses exactly these forms. They are generated from a single module, `notation.py`.

| Object | On screen |
|---|---|
| Many-sorted signature | $\mathbf{\Sigma}=(S,\Sigma)$; $\sigma\in\Sigma_{\mathbf{s},s}$, with $\mathbf{s}\in S^{\star}$ the arity and $s\in S$ the sort |
| Running example | $S=\{s,t\}$, $\sigma\in\Sigma_{(s,t),s}$, $\tau\in\Sigma_{(s),t}$ |
| (Partial) algebra | $\mathbf{A}=(A,F)$, $A=(A_s)_{s\in S}$, $\sigma^{\mathbf{A}}\colon A_{\mathbf{s}}\to A_{s}$ (partial: $\sigma^{\mathbf{A}}\colon A_{\mathbf{s}}\dashrightarrow A_s$); $\mathsf{Alg}(\Sigma)$, $\mathsf{PAlg}(\Sigma)$ |
| Existence equation | $P\overset{\mathrm e}{=}Q$; QE-equation $\bigwedge_j(P_j\overset{\mathrm e}{=}Q_j)\to(P\overset{\mathrm e}{=}Q)$ |
| Homogeneous $n$-category | $\mathsf{C}=(C,(\xi_k)_{k\in n})$, $\xi_k=(\circ^{k},\mathrm{sc}^{k},\mathrm{tg}^{k})$; $k$-cells $C_k=\{f\in C\mid f=\mathrm{sc}^{k}(f)\}$ |
| Categorial algebras | $\calg{A}$ (bold sans-serif), $\mathsf{A}=(\mathsf{A}_s)_{s\in S}$, $\sigma^{\calg{A}}\colon\mathsf{A}_{\mathbf{s}}\to\mathsf{A}_s$; $\mathsf{nCatAlg}(\mathbf{\Sigma})$, $\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})$, $\omega\mathsf{CatAlg}(\mathbf{\Sigma})$, $\omega\mathsf{Cat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})$ |
| Homogeneous extension | $\mathbf{\Sigma}^{(n)}$: $\mathrm{sc}^{k}_{s},\mathrm{tg}^{k}_{s}\in\Sigma^{(n)}_{(s),s}$, $\circ^{k}_{s}\in\Sigma^{(n)}_{(s,s),s}$ ($k\in n$, $s\in S$); $\mathrm{def}(\circ^{k}_{s})=\{\mathrm{sc}^{k}_{s}(v^{s}_{0})\overset{\mathrm e}{=}\mathrm{tg}^{k}_{s}(v^{s}_{1})\}$ |
| Heterogeneous extension | $\mathbf{\Sigma}^{\mathrm{htg}(n)}$, sorts $(k,s)\in(n+1)\times S$: $\sigma_k$, $\mathrm{sc}^{(j,k)}_{s}$, $\mathrm{tg}^{(j,k)}_{s}$, $\mathrm{i}^{(k,j)}_{s}$, $\circ^{(j,k)}_{s}$ ($j<k$); $\mathrm{def}(\circ^{(j,k)}_{s})=\{\mathrm{sc}^{(j,k)}_{s}(v^{(k,s)}_{0})\overset{\mathrm e}{=}\mathrm{tg}^{(j,k)}_{s}(v^{(k,s)}_{1})\}$; carriers $A_{(k,s)}$ |
| Specifications | $\mathsf{nCatAlg}(\mathbf{\Sigma})=\mathsf{EPAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}})$, $\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})=\mathsf{EPAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{\mathrm{htg}(n)}})$ |
| hep-signature | $\mathbf{\Sigma}=(S,\Sigma,\mathrm{def}^{(S,\Sigma)})$, relation $\lhd$ well-founded |
| Derivor | $\mathbf{c}=(\varphi,c)\colon\mathbf{\Sigma}\to\mathbf{\Lambda}$, $\varphi\colon S\to T$, $c(\sigma)\in\mathrm{T}_{\Lambda}(\mathord{\downarrow}\varphi^{\star}(\mathbf{s}))_{\varphi(s)}$; category $\mathsf{Sig}_{\mathfrak{d}}$ |
| Generalized hep-derivor | $\mathbf{c}=(\varphi,c,\mathrm{Dom}^{(\varphi,c)})$, domains $\mathrm{Dom}^{(\varphi,c)}_{s}$; transformed algebra $\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{B})$, cells $B_{\mathrm{Dom}^{(\varphi,c)}}$ |
| Derivors of the four functors | $\mathbf{Gd}^{(n)}_{\mathbf{\Sigma}}\colon\mathbf{\Sigma}^{\mathrm{htg}(n)}\to\mathbf{\Sigma}^{(n)}$, $\mathbf{Uf}^{(n)}_{\mathbf{\Sigma}}\colon\mathbf{\Sigma}^{(n)}\to\mathbf{\Sigma}^{\mathrm{htg}(n)}$, $\mathbf{Ds}^{(n,m)}_{\mathbf{\Sigma}}\colon\mathbf{\Sigma}^{(n)}\to\mathbf{\Sigma}^{(m)}$, $\mathbf{Tr}^{(m,n)}_{\mathbf{\Sigma}}\colon\mathbf{\Sigma}^{(m)}\to\mathbf{\Sigma}^{(n)}$ (and $\mathrm{htg}$ versions) |
| The four functors | $\mathrm{Gd}^{(n)}_{\mathbf{\Sigma}}$, $\mathrm{Uf}^{(n)}_{\mathbf{\Sigma}}$, $\mathrm{Ds}^{(n,m)}_{\mathbf{\Sigma}}$, $\mathrm{Ds}^{\mathrm{htg}(n,m)}_{\mathbf{\Sigma}}$, $\mathrm{Tr}^{(m,n)}_{\mathbf{\Sigma}}$, $\mathrm{Tr}^{\mathrm{htg}(m,n)}_{\mathbf{\Sigma}}$; in dimension ω: $\mathrm{Tr}^{(n,\omega)}_{\mathbf{\Sigma}}$, $\mathrm{Ds}^{(\omega,m)}_{\mathbf{\Sigma}}$, $\mathrm{Gd}^{(\omega)}_{\mathbf{\Sigma}}$, $\mathrm{Uf}^{(\omega)}_{\mathbf{\Sigma}}$ |
| Unification in ω | $[B]_s=\coprod_{k\in\omega}B_{(k,s)}/\Theta_s$, classes $[x]_k$ |
| Change of signature | $\mathbf{c}^{(n)}$, $\mathbf{c}^{\mathrm{htg}(n)}$, $\varphi^{\mathrm{htg}(n)}(k,s)=(k,\varphi(s))$; functors $\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}$, $\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}$ |

**Abbreviation rule.** Scene 8 shows each functor with its full indices, then the note "from now on we drop $\mathbf{\Sigma}$". After that, the functors are written with their dimensions and without the signature: $\mathrm{Gd}^{(n)}$, $\mathrm{Ds}^{(n,m)}$, $\mathrm{Ds}^{\mathrm{htg}(n,m)}$, … The exception is Scene 19, where the signature changes: there $\mathbf{\Sigma}$ and $\mathbf{\Lambda}$ are written again. Bare forms such as $\mathrm{Gd}$, $\mathrm{Ds}$ or $\mathrm{Gd}_{\Sigma}$ never appear.

**No references to the paper on screen.** The video shows no numbers of definitions or results, no section numbers and no link to the paper.

---

## Visual conventions

| Element | Representation | Colour |
|---|---|---|
| Sort $s$ / sort $t$ | fill of the container (bag, cloud, column of drawers) | blue-grey `#7A8CB8` / rose `#B87A9C` |
| 0-cells, 1-cells, 2-cells, 3-cells | dot; arrow; globe (⇓ between two arrows); ⇛ between two 2-cells | white; blue; yellow; grey-violet |
| Identity cells | as above, dashed | grey |
| Operation symbols σ, τ (and their copies $\sigma_k$, $\tau_k$) | rounded box with the symbol | green |
| Structure symbols sc, tg, i, ∘ | small labels on thin arrows | light grey |
| Domain conditions (def) | `\overset{\mathrm e}{=}` | yellow |
| Derivors (bold) and domains (Dom) | dashed arrows, the "gate" filter | teal `#4FD1C5` |
| Functors | thick arrows | orange |

**Layout.** Every scene has a heading at the top. A progress bar at the bottom shows five parts: *algebras*, *presentations*, *hep-derivors*, *dimensions*, *signatures*. The main diagram goes in the centre; formal statements go in a framed box. Minimum scale 0.6 for text and 0.65 for formulas. Cells inside bags and drawers are placed on a regular grid by dimension. After each new formula, keep at least 1.5 s of still image before the fade-out.

**Recurring animations.**
- *Gate:* a teal dashed bar labelled with the existence equations of a domain. Cells that satisfy them go through; the others fade to 25 %.
- *Square → cube:* the square of the four functors (Scene 8) is reused in Scenes 13–16, 18 and 19. The summary cube of Scene 20 is built from it, and is glimpsed at the start (Scene 1) as a map of the video.
- *Recap cards:* a small card at the end of each part (Scenes 5, 8, 12, 18) lists what has been introduced so far.
- *Two levels:* the bold derivor between signatures is drawn above, and the functor it induces between categories of algebras below, in the opposite direction.

---

## Part I — Algebras

## Scene 1 — Opening

**Visuals.**
1. Title card: "Higher-order many-sorted categorial algebras" written; "via generalized hep-derivors" in teal below; the authors fade in.
2. **Map of the video.** For about four seconds, the summary cube of Scene 20 appears faded, behind a caption: "by the end, we will read this picture". It then dissolves.
3. The title moves up. Left: a globe $f\Rightarrow g$ between two 0-cells, then a ⇛ hint ("cells of every dimension"). Right: two clouds of different colours ($A_s$, $A_t$) with a green box σ taking one point from each ("several sorts, operations between them").
4. The two pictures merge: each cloud becomes a small higher category (the globe inside a coloured bag), and σ now acts on cells.
5. Back to the title; the subtitle is circumscribed in teal.

**Voice-over.**
> Categories have objects and arrows. Higher-order categories also have arrows between arrows, and arrows between those. Many-sorted algebras, in turn, have one set of elements for each sort, and operations between them. A higher-order many-sorted categorial algebra puts both together. This video shows how to relate its presentations and its dimensions with a single tool: generalized hep-derivors. By the end, we will be able to read the whole picture.

## Scene 2 — Many-sorted signatures and partial algebras

**Visuals.**
1. Heading "Many-sorted signatures". $\mathbf{\Sigma}=(S,\Sigma)$; $S=\{s,t\}$ (two coloured chips).
2. The ranks: $\sigma\in\Sigma_{(s,t),s}$ and $\tau\in\Sigma_{(s),t}$, each with a small arity diagram (input chips → output chip).
3. An algebra $\mathbf{A}$: two clouds $A_s$ (blue-grey) and $A_t$ (rose).
   - $\sigma^{\mathbf{A}}\colon A_s\times A_t\to A_s$: a point of $A_s$ and a point of $A_t$ enter the σ box, and a point of $A_s$ comes out.
   - $\tau^{\mathbf{A}}\colon A_s\to A_t$: a point crosses from $A_s$ to $A_t$.
4. Partial algebra: $\sigma^{\mathbf{A}}\colon A_s\times A_t\dashrightarrow A_s$; one pair is refused (red cross). Bottom: $\mathsf{Alg}(\Sigma)$, $\mathsf{PAlg}(\Sigma)$.

**Voice-over.**
> A many-sorted signature has a set of sorts, and operation symbols, each with an arity, which is a word of sorts, and a sort. Our running example has two sorts, s and t, and two symbols: sigma, with arity s t and sort s, and tau, with arity s and sort t. An algebra for this signature has a set for each sort. It interprets sigma as a function that takes an element of sort s and one of sort t, and returns one of sort s; and tau as a function from sort s to sort t. In a partial algebra, an operation may be undefined at some arguments.

## Scene 3 — A category is a partial algebra

**Visuals.** With the paper's notation:
1. $X\xrightarrow{f}Y\xrightarrow{g}Z$; dashed $\mathrm{sc}(f)$, $\mathrm{tg}(f)$.
2. The objects turn into identities $\mathrm{sc}(f)$, $\mathrm{tg}(f)$; all cells slide into one bag $C$ ("homogeneous category").
3. $g\circ f\text{ is defined}\iff\mathrm{sc}(g)\overset{\mathrm e}{=}\mathrm{tg}(f)$, with the label "existence equation" under $\overset{\mathrm e}{=}$.
4. The laws (C1)–(C5), for instance $\mathrm{sc}(\mathrm{sc}(f))=\mathrm{sc}(f)$, $f\circ\mathrm{sc}(f)=f$, $h\circ(g\circ f)=(h\circ g)\circ f$, framed in green as "QE-equations".

**Voice-over.**
> Here is the first key idea. A category can be seen as a partial algebra. Take a single set of cells. Each cell has a source and a target, given by two unary operations. Objects are identified with their identities, so the source of an arrow is itself a cell. Composition is a partial operation: g composed with f exists exactly when the source of g equals the target of f. This domain condition is an existence equation. The category laws become quasi-existence equations, or QE-equations.

## Scene 4 — Homogeneous n-categories

**Visuals.**
1. $\mathsf{C}=(C,(\xi_k)_{k\in n})$, $\xi_k=(\circ^{k},\mathrm{sc}^{k},\mathrm{tg}^{k})$: one bag $C$ with $n$ coloured "layers" of structure.
2. A globe $\alpha\colon f\Rightarrow f'$ in the bag. $k$-cells: $C_k=\{f\in C\mid f=\mathrm{sc}^{k}(f)\}$; the 0-cells and 1-cells light up as fixed points of $\mathrm{sc}^{0}$, $\mathrm{sc}^{1}$.
3. Horizontal $\beta\circ^{0}\alpha$ and vertical $\beta\circ^{1}\alpha$.
4. The 2×2 grid and the interchange law (2C3): $(g'\circ^{0}f')\circ^{1}(g\circ^{0}f)=(g'\circ^{1}g)\circ^{0}(f'\circ^{1}f)$. Here the primes mark the neighbouring cell in the grid, as in the paper.

**Voice-over.**
> A homogeneous n-category carries n such structures of category on the same set of cells, one for each dimension k below n, each with its own sources, targets and composition. A cell is a k-cell when it is its own k-source. For two dimensions j below k, the structures must be compatible. Given a grid of four cells, composing rows first or columns first gives the same result. This is the interchange law.

## Scene 5 — Many-sorted n-categorial algebras

**Visuals.**
1. Two coloured bags $\mathsf{A}_s$, $\mathsf{A}_t$, each a homogeneous $n$-category: $\mathsf{A}=(\mathsf{A}_s)_{s\in S}$.
2. The operations:
   - $\sigma^{\calg{A}}\colon\mathsf{A}_s\times\mathsf{A}_t\to\mathsf{A}_s$: a globe of sort $s$ and a globe of sort $t$ enter the σ box, and a globe of sort $s$ comes out;
   - $\tau^{\calg{A}}\colon\mathsf{A}_s\to\mathsf{A}_t$.
3. Functoriality, with cells $f,g$ of sort $s$ and $a,b$ of sort $t$ (no primes, so as not to clash with Scene 4):
   - $\sigma(g\circ^{k}f,\;b\circ^{k}a)=\sigma(g,b)\circ^{k}\sigma(f,a)$;
   - $\mathrm{sc}^{k}(\sigma(f,a))=\sigma(\mathrm{sc}^{k}(f),\mathrm{sc}^{k}(a))$.

   Caption: "$\sigma^{\calg{A}}$ is an $n$-functor on the product $\mathsf{A}_{(s,t)}=\mathsf{A}_s\times\mathsf{A}_t$, computed componentwise".
4. Boxed: "a many-sorted $n$-categorial $\mathbf{\Sigma}$-algebra: a homogeneous $n$-category for each sort + every operation symbol an $n$-functor"; "$n=0$: ordinary $\Sigma$-algebras".
5. Homomorphisms: two algebras $\calg{A}$, $\calg{B}$ side by side and $H=(H_s,H_t)$, one $n$-functor per sort (orange arrows between the bags of the same colour). A commuting square:
   - $H_s(\sigma^{\calg{A}}(f,a))=\sigma^{\calg{B}}(H_s(f),H_t(a))$;
   - the category $\mathsf{nCatAlg}(\mathbf{\Sigma})$.
6. **Recap of Part I** (small card, bottom right): "signature $\mathbf{\Sigma}$ with sorts; partial algebras; $n$-categories; $n$-categorial $\mathbf{\Sigma}$-algebras".

**Voice-over.**
> A many-sorted n-categorial algebra has a homogeneous n-category for every sort, and interprets every operation symbol as an n-functor, defined on the product of the categories of its arity. So sigma takes a pair of cells, one of sort s and one of sort t, and preserves sources, targets and compositions in every dimension. For n equal to zero we recover ordinary many-sorted algebras. A homomorphism between two such algebras is an n-functor for every sort, and these functors commute with the operations. Together, they form the category of n-categorial Sigma-algebras.

## Part II — Presentations

## Scene 6 — The homogeneous categorial extension of a signature

**Visuals.**
1. Heading "The homogeneous categorial extension $\mathbf{\Sigma}^{(n)}$". The list of symbols of $\Sigma$: $\sigma\colon(s,t)\to s$, $\tau\colon(s)\to t$.
2. The list grows, dimension by dimension, for each sort:
   - $\mathrm{sc}^{k}_{s},\mathrm{tg}^{k}_{s}\colon(s)\to s$ and $\circ^{k}_{s}\colon(s,s)\to s$;
   - $\mathrm{sc}^{k}_{t},\mathrm{tg}^{k}_{t}\colon(t)\to t$ and $\circ^{k}_{t}\colon(t,t)\to t$;
   - for $k=0,1,\dots,n-1$, colour-coded by dimension.
3. Domain conditions: $\mathrm{def}(\circ^{k}_{s})=\{\mathrm{sc}^{k}_{s}(v^{s}_{0})\overset{\mathrm e}{=}\mathrm{tg}^{k}_{s}(v^{s}_{1})\}$ in yellow; all the other symbols: $\varnothing$.
4. The relation $\lhd$: arrows from $\circ^{k}_{s}$ down to $\mathrm{sc}^{k}_{s}$, $\mathrm{tg}^{k}_{s}$; "well-founded: a **hep-signature** (hierarchical equationally partial)".
5. **ep-algebras.** A partial algebra over a hep-signature is an *ep-algebra* when $\mathrm{Dom}(\sigma^{\mathbf{A}})=A_{\mathrm{def}(\sigma)}$ for every symbol, i.e. each operation is defined **exactly** where its domain conditions hold.
   - Animation: the pairs of cells of $\mathsf{A}_s$ that satisfy $\mathrm{sc}^{k}_{s}(v^{s}_{0})\overset{\mathrm e}{=}\mathrm{tg}^{k}_{s}(v^{s}_{1})$ light up; these are exactly the pairs where $\circ^{k}_{s}$ is defined.
   - Category: $\mathsf{EPAlg}$.
6. Framed: $\mathsf{nCatAlg}(\mathbf{\Sigma})=\mathsf{EPAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}})$, "$\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}}$: QE-equations".

**Voice-over.**
> All this structure can be written as a signature. The homogeneous categorial extension of Sigma adds, for every sort and every dimension k below n, a k-source, a k-target and a k-composition. Each composition comes with a domain condition, an existence equation: the composite of two cells is defined exactly when the k-source of the first equals the k-target of the second. These conditions only use sources and targets, which have none, so they form a well-founded hierarchy. This makes it a hierarchical equationally partial signature, or hep-signature. Over such a signature, an ep-algebra is a partial algebra in which every operation is defined exactly where its domain conditions hold: composition, exactly at the composable pairs. And the n-categorial algebras are exactly the ep-algebras over this signature that satisfy a set of QE-equations.

## Scene 7 — The heterogeneous categorial extension

**Visuals.**
1. Heading "The heterogeneous categorial extension $\mathbf{\Sigma}^{\mathrm{htg}(n)}$". Caption: "heterogeneous: by dimension (not by sort)". A grid of drawers, with rows $k=0,\dots,n$ and columns $s$ (blue-grey) and $t$ (rose). Each drawer is labelled with its sort $(k,s)$ or $(k,t)$, and later with its carrier $A_{(k,s)}$.
2. In each row, the copies $\sigma_k\colon((k,s),(k,t))\to(k,s)$ and $\tau_k\colon((k,s))\to(k,t)$ (green, horizontal arrows inside the row).
3. In each column, between rows $j<k$:
   - $\mathrm{sc}^{(j,k)}_{s},\mathrm{tg}^{(j,k)}_{s}$ going down and $\mathrm{i}^{(k,j)}_{s}$ going up;
   - $\circ^{(j,k)}_{s}$ on row $k$, with $\mathrm{def}(\circ^{(j,k)}_{s})=\{\mathrm{sc}^{(j,k)}_{s}(v^{(k,s)}_{0})\overset{\mathrm e}{=}\mathrm{tg}^{(j,k)}_{s}(v^{(k,s)}_{1})\}$.
4. **A concrete example**, for $n=1$:
   - $A_{(0,s)}=\{x,y\}$, $A_{(1,s)}=\{f,\mathrm{i}(x),\mathrm{i}(y)\}$ with $f\colon x\to y$;
   - $A_{(0,t)}=\{z\}$, $A_{(1,t)}=\{a,\mathrm{i}(z)\}$ with $a\colon z\to z$.

   The copy $\sigma_1$ takes $f$ and $a$ and gives a 1-cell $\sigma_1(f,a)$ of sort $(1,s)$. Its source is computed in row 0: $\mathrm{sc}^{(0,1)}_{s}(\sigma_1(f,a))=\sigma_0(\mathrm{sc}^{(0,1)}_{s}(f),\mathrm{sc}^{(0,1)}_{t}(a))=\sigma_0(x,z)$.
5. Framed: $\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})=\mathsf{EPAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{\mathrm{htg}(n)}})$.
6. Split screen: left, the two bags $\mathsf{A}_s$, $\mathsf{A}_t$ and $\mathsf{nCatAlg}(\mathbf{\Sigma})$; right, the grid of drawers and $\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})$; between them "$\simeq$ ?".

**Voice-over.**
> The heterogeneous presentation separates the cells by dimension; here, heterogeneous refers to the dimensions, not to the sorts. Its categorial extension has a sort for every pair made of a dimension up to n and a sort of Sigma: a grid of drawers. Each operation symbol gets one copy in every dimension, acting on the cells of that dimension. Sources and targets go down to every lower dimension, identities go up, and every composition has its domain condition. For instance, in dimension one, the copy of sigma takes an arrow of sort s and an arrow of sort t, and returns an arrow of sort s, whose source is computed by the copy of sigma in dimension zero. Again, the heterogeneous n-categorial algebras are the ep-algebras that satisfy a set of QE-equations. So we have two categories of algebras for the same signature. Are they the same?

## Scene 8 — Four functors, one mechanism?

**Visuals.**
1. The square of categories, for $m\le n$:
   - top: $\mathsf{mCatAlg}(\mathbf{\Sigma})$, $\mathsf{mCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})$;
   - bottom: $\mathsf{nCatAlg}(\mathbf{\Sigma})$, $\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})$.
2. Horizontal pairs: $\mathrm{Gd}^{(m)}_{\mathbf{\Sigma}}$ / $\mathrm{Uf}^{(m)}_{\mathbf{\Sigma}}$ and $\mathrm{Gd}^{(n)}_{\mathbf{\Sigma}}$ / $\mathrm{Uf}^{(n)}_{\mathbf{\Sigma}}$, labelled "change the presentation".
3. Vertical pairs: $\mathrm{Ds}^{(n,m)}_{\mathbf{\Sigma}}$ / $\mathrm{Tr}^{(m,n)}_{\mathbf{\Sigma}}$ on the left and $\mathrm{Ds}^{\mathrm{htg}(n,m)}_{\mathbf{\Sigma}}$ / $\mathrm{Tr}^{\mathrm{htg}(m,n)}_{\mathbf{\Sigma}}$ on the right, labelled "change the dimension".
4. Note (grey box): "from now on we drop $\mathbf{\Sigma}$: $\mathrm{Gd}^{(n)}$, $\mathrm{Ds}^{(n,m)}$, …; heterogeneous symbols carry $\mathrm{htg}$, homogeneous ones no marker"; the labels lose their subscript $\mathbf{\Sigma}$ (`TransformMatchingTex`).
5. Below: "one mechanism, for every signature?" and a teal dashed arrow $\mathbf{\Sigma}\dashrightarrow\mathbf{\Lambda}$, "a translation of signatures?".
6. **Recap of Part II** (small card): "two categorial extensions $\mathbf{\Sigma}^{(n)}$, $\mathbf{\Sigma}^{\mathrm{htg}(n)}$; two categories of algebras; four functors".

**Voice-over.**
> To compare them, we need four functors. Graduation and unification change the presentation. Discretization and truncation change the dimension, between m and n. Each of them depends on the signature and on the dimensions; from now on we leave the signature out of the notation. So far we have two categorial extensions of the signature, two categories of algebras, and four functors between them. We would like to obtain all four functors from a single mechanism, which works for every signature at once. The natural candidate is a translation between signatures.

## Part III — Generalized hep-derivors

## Scene 9 — Derivors

**Visuals.**
1. Heading "Derivors". $\mathbf{c}=(\varphi,c)\colon\mathbf{\Sigma}\to\mathbf{\Lambda}$; $\varphi\colon S\to T$; $\sigma\in\Sigma_{\mathbf{s},s}\ \mapsto\ c(\sigma)\in\mathrm{T}_{\Lambda}(\mathord{\downarrow}\varphi^{\star}(\mathbf{s}))_{\varphi(s)}$.
2. Example, a derivor $\mathbf{c}\colon\mathbf{\Sigma}\to\mathbf{\Sigma}$ with $\varphi=\mathrm{id}_S$:
   - $c(\sigma)=\sigma(v^{s}_{0},\tau(v^{s}_{0}))$ and $c(\tau)=\tau(v^{s}_{0})$;
   - the sort chips check that each term has the right sort: σ's term has sort $s$, τ's has sort $t$;
   - the term $c(\sigma)$ is drawn as a small tree, and $\tau(v^{s}_{0})$ fills the slot of sort $t$.
3. Two levels:
   - above, $\mathbf{c}\colon\mathbf{\Sigma}\to\mathbf{\Lambda}$ (teal);
   - below, the induced functor $\mathbf{c}^{\ast}\colon\mathsf{Alg}(\Lambda)\to\mathsf{Alg}(\Sigma)$ (orange, opposite direction).
4. Animation of the induced functor: a $\Lambda$-algebra $\mathbf{B}$ (cloud). Its carrier of sort $\varphi(s)$ becomes the carrier of sort $s$ of $\mathbf{c}^{\ast}(\mathbf{B})$, and σ is computed by evaluating the tree $c(\sigma)$ in $\mathbf{B}$.

**Voice-over.**
> A derivor from Sigma to Lambda sends every sort to a sort, and every operation symbol to a term of the matching sort, in variables of the matching sorts. For instance, a derivor from Sigma to itself may send sigma to the term sigma of v zero and tau of v zero, where v zero is a variable of sort s. A derivor induces a functor in the opposite direction, from Lambda-algebras to Sigma-algebras. It takes a Lambda-algebra, uses its carrier of the image sort as the carrier of each sort, and interprets each symbol as its term. The translation goes from Sigma to Lambda, so the algebras go from Lambda back to Sigma.

## Scene 10 — Why derivors are not enough

**Visuals.**
1. Heading "… but derivors are not enough". Split screen.
2. Left panel, obstacle 1 (graduation):
   - a bag $\mathsf{A}_s$ with cells of dimensions 0, 1 and 2, and the target drawer $A_{(k,s)}$;
   - the gate $v^{s}_{0}\overset{\mathrm e}{=}\mathrm{sc}^{k}_{s}(v^{s}_{0})$: only the $k$-cells pass;
   - caption "keep only part of the elements: a derivor keeps the whole carrier".
3. Right panel, obstacle 2 (discretization):
   - $\circ^{k}_{s}\mapsto v^{s}_{0}$, "defined at every pair";
   - then "$v^{s}_{0}\circ^{k}_{s}v^{s}_{1}$ must be defined $\iff v^{s}_{0}=v^{s}_{1}$" and, in red, "no term can say this".
   - Small example: a set $B=\{x,y\}$ seen as a discrete category; the pair $(x,x)$ is composable, the pair $(x,y)$ is not.

**Voice-over.**
> But ordinary derivors are not enough, for two reasons. First, some functors keep only part of the elements, whereas a derivor keeps the whole carrier: graduation keeps, as cells of dimension k and sort s, only the cells that are their own k-source. Second, some domains cannot be expressed by any term. Discretization interprets a higher composition by its first argument, which is always defined. And yet, in the discretized algebra, two cells must be composable only when they are equal: a set becomes a discrete category, in which a cell can only be composed with itself.

## Scene 11 — Generalized hep-derivors

**Visuals.**
1. Heading "Generalized hep-derivors". $\mathbf{c}=(\varphi,c,\mathrm{Dom}^{(\varphi,c)})\colon\mathbf{\Sigma}\to\mathbf{\Lambda}$ between hep-signatures.
2. $s\mapsto\varphi(s)$ together with $\mathrm{Dom}^{(\varphi,c)}_{s}$ (teal), "existence equations in one variable $v^{\varphi(s)}_{0}$"; $\sigma\mapsto c(\sigma)$, "a term".
3. A partial $\Lambda$-algebra $\mathbf{B}$ (cloud); the gate $\mathrm{Dom}^{(\varphi,c)}_{s}$; the selected elements form the cells $B_{\mathrm{Dom}^{(\varphi,c)}}$ of $\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{B})$.
4. "$\sigma^{\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{B})}$ is defined at $\mathbf{b}$ $\iff$", followed by three checks (colours as in the conventions):
   - (yellow) $\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{B})\models\mathrm{def}(\sigma)[\mathbf{b}]$;
   - (green) $c(\sigma)^{\mathbf{B}}$ is defined at $\mathbf{b}$;
   - (teal) $c(\sigma)^{\mathbf{B}}(\mathbf{b})$ is a cell.
5. The two obstacles of Scene 10 come back, solved:
   - the gate of graduation is a domain;
   - the diagonal of discretization is the first check.
6. The hierarchy $\lhd$ lights up from the bottom: "defined by well-founded recursion".

**Voice-over.**
> The solution adds domains to derivors. A generalized hep-derivor between hep-signatures sends every sort to a sort together with a domain, a set of existence equations in one variable, and every operation symbol to a term. The transformed algebra keeps, as cells, the elements that satisfy the domains. An operation is defined at some cells when three conditions hold: its domain conditions hold in the transformed algebra itself, its term is defined, and the value is again a cell. The domains solve the first obstacle, and the first condition solves the second. Since the hierarchy is well-founded, this is a valid definition by recursion.

## Scene 12 — Weak algebras and lax composition

**Visuals.**
1. $\mathrm{Dom}(\sigma^{\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{B})})\subseteq B_{\mathrm{def}(\sigma)}$: "always a **weak** $\mathbf{\Sigma}$-algebra: defined at most where the domain conditions hold". This is contrasted with the equality that defines an ep-algebra (Scene 6). Then: "an ep-algebra $\iff$ on the domain conditions, the terms are defined and give cells".
2. **Split screen for the example.**
   - Left, fixed throughout, the algebra $\mathbf{C}$: $C_w=\{0,1\}$, $z^{\mathbf{C}}=0$, $o^{\mathbf{C}}=1$.
   - Right, the chain $\mathbf{\Sigma}\xrightarrow{\ \mathbf{c}\ }\mathbf{\Lambda}\xrightarrow{\ \mathbf{d}\ }\mathbf{\Omega}$, one signature per row:
     - $\mathbf{\Sigma}$: a sort $s$, no symbols;
     - $\mathbf{\Lambda}$: a sort $t$ and a symbol $u\in\Lambda_{(t),t}$;
     - $\mathbf{\Omega}$: a sort $w$ and constants $z,o\in\Omega_{\lambda,w}$.

   Each step highlights its row on the right and acts on $\mathbf{C}$ on the left.
3. Step $\mathbf{d}$ (row $\mathbf{\Lambda}\to\mathbf{\Omega}$ highlighted):
   - $\mathrm{Dom}^{\mathbf{d}}_{t}=\{v^{w}_{0}\overset{\mathrm e}{=}z\}$: the gate keeps $0$;
   - $d(u)=o$: the value $1$ is not a cell (red cross), so $u$ is nowhere defined in $\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{C})$.
4. Step $\mathbf{c}$ (row $\mathbf{\Sigma}\to\mathbf{\Lambda}$ highlighted): $\mathrm{Dom}^{\mathbf{c}}_{s}=\{u(v^{t}_{0})\overset{\mathrm e}{=}u(v^{t}_{0})\}$ selects the points where $u$ is defined. Nothing passes: $\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{C}))=\varnothing$.
5. Composite (both rows merge into $\mathbf{d}\circ\mathbf{c}$): $\mathrm{Dom}^{\mathbf{d}\circ\mathbf{c}}_{s}=\{v^{w}_{0}\overset{\mathrm e}{=}z,\ o\overset{\mathrm e}{=}o\}$ keeps $0$, so $(\mathbf{d}\circ\mathbf{c})^{\ast}_{\mathfrak{gd}}(\mathbf{C})$ has the single cell $0$.
6. Conclusion:
   - $\kappa^{\mathbf{c},\mathbf{d}}_{\mathbf{C}}\colon\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{C}))\hookrightarrow(\mathbf{d}\circ\mathbf{c})^{\ast}_{\mathfrak{gd}}(\mathbf{C})$, here $\varnothing\subsetneq\{0\}$;
   - "a normal lax indexed category".
7. **Recap of Part III** (small card): "generalized hep-derivor = sorts with domains + symbols with terms; transformed algebra by recursion; lax under composition".

**Voice-over.**
> The transformed algebra is always a weak algebra: its operations are defined at most where their domain conditions hold. There is a simple criterion for it to be an ep-algebra. Composition, however, is subtle. Take an algebra with a single sort and two constants, zero and one. A first derivor selects only zero, and interprets a unary operation u by the constant one. Then u is nowhere defined, because one is not a cell. A second derivor selects the points where u is defined, and nothing is left; but the composite derivor still keeps zero. So there is only a natural inclusion of the composite of the induced functors into the functor induced by the composite, and the induced functors form a normal lax indexed category.

## Part IV — Dimensions

## Scene 13 — Graduation

**Visuals.**
1. Two levels:
   - above, the derivor $\mathbf{Gd}^{(n)}\colon\mathbf{\Sigma}^{\mathrm{htg}(n)}\to\mathbf{\Sigma}^{(n)}$ (teal, left to right);
   - below, the functor $\mathrm{Gd}^{(n)}\colon\mathsf{nCatAlg}(\mathbf{\Sigma})\to\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})$ (orange, right to left);
   - a reminder in grey: "the functor goes against the derivor".
2. The rules, one at a time:
   - $(k,s)\mapsto s$;
   - $\mathrm{Dom}_{(k,s)}=\{v^{s}_{0}\overset{\mathrm e}{=}\mathrm{sc}^{k}_{s}(v^{s}_{0})\}$ for $k\in n$, and $\mathrm{Dom}_{(n,s)}=\varnothing$;
   - $\sigma_k\mapsto\sigma(v^{s}_{0},v^{t}_{1})$;
   - $\mathrm{sc}^{(j,k)}_{s}\mapsto\mathrm{sc}^{j}_{s}(v^{s}_{0})$;
   - $\mathrm{i}^{(k,j)}_{s}\mapsto v^{s}_{0}$;
   - $\circ^{(j,k)}_{s}\mapsto v^{s}_{0}\circ^{j}_{s}v^{s}_{1}$.
3. Animation: the cells of the bag $\mathsf{A}_s$ pass the gate of each row and fly to column $s$ of the grid, at the row of their dimension; the same for $\mathsf{A}_t$ and column $t$. A lower cell lands in **several** rows: a 0-cell is also a 1-cell and a 2-cell, and lands in the row of each.

**Voice-over.**
> Graduation is induced by a generalized hep-derivor from the heterogeneous extension to the homogeneous one. As always, the functor goes the other way: the derivor translates heterogeneous symbols into homogeneous terms, so it turns homogeneous algebras into heterogeneous ones. The derivor sends the sort of dimension k and sort s to s, with the domain: v zero equals its k-source. So the drawer of dimension k receives the k-cells of the right sort; a cell of low dimension is a k-cell for every larger k, and lands in each of those drawers. Every copy of sigma goes to sigma itself, every heterogeneous source to the homogeneous source, every composition to the homogeneous composition, and every identity to the variable itself, because in the homogeneous presentation a lower cell is already its own identity.

## Scene 14 — Unification, and the equivalence

**Visuals.**
1. Two levels: $\mathbf{Uf}^{(n)}\colon\mathbf{\Sigma}^{(n)}\to\mathbf{\Sigma}^{\mathrm{htg}(n)}$ above, and $\mathrm{Uf}^{(n)}\colon\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})\to\mathsf{nCatAlg}(\mathbf{\Sigma})$ below.
2. The rules:
   - $s\mapsto(n,s)$, with empty domains;
   - $\sigma\mapsto\sigma_n(v^{(n,s)}_{0},v^{(n,t)}_{1})$;
   - $\mathrm{sc}^{k}_{s}\mapsto\mathrm{i}^{(n,k)}_{s}(\mathrm{sc}^{(k,n)}_{s}(v^{(n,s)}_{0}))$;
   - $\circ^{k}_{s}\mapsto v^{(n,s)}_{0}\circ^{(k,n)}_{s}v^{(n,s)}_{1}$.
3. Animation: only row $n$ of each column is kept and poured into the bag of its sort. The source of a top cell is computed by going down to row $k$ and coming back up with the identity (dashed path).
4. The equivalence:
   - $\mathrm{Uf}^{(n)}\circ\mathrm{Gd}^{(n)}=\mathrm{Id}$ (green circumscribe);
   - $\theta\colon\mathrm{Id}\cong\mathrm{Gd}^{(n)}\circ\mathrm{Uf}^{(n)}$, with $\theta$ sending $u\in A_{(k,s)}$ to $\mathrm{i}^{(n,k)}_{s}(u)$ (yellow circumscribe);
   - $\mathrm{Gd}^{(n)}\dashv\mathrm{Uf}^{(n)}$, unit $\mathrm{id}$, counit $\theta^{-1}$: an adjoint equivalence.

**Voice-over.**
> Unification goes the other way. It sends every sort s to the top drawer of s, each symbol to its copy in the top dimension, each k-composition to the composition of top cells along dimension k, and each k-source to the identity of the heterogeneous source. Unifying after graduating gives back exactly what we started with. Graduating after unifying gives a naturally isomorphic algebra: each lower cell is replaced by its identity in the top dimension. So graduation is left adjoint to unification, in an adjoint equivalence whose unit is the identity: the two presentations give equivalent categories, and nothing is lost by choosing either of them.

## Scene 15 — Discretization and truncation

**Visuals.**
1. A tower $\mathsf{0CatAlg}(\mathbf{\Sigma})$, $\mathsf{1CatAlg}(\mathbf{\Sigma})$, $\mathsf{2CatAlg}(\mathbf{\Sigma})$, ….
2. Truncation:
   - derivor $\mathbf{Tr}^{(m,n)}\colon\mathbf{\Sigma}^{(m)}\hookrightarrow\mathbf{\Sigma}^{(n)}$ (the inclusion), with $\mathrm{Dom}_{s}=\{v^{s}_{0}\overset{\mathrm e}{=}\mathrm{sc}^{m}_{s}(v^{s}_{0})\}$;
   - functor $\mathrm{Tr}^{(m,n)}\colon\mathsf{nCatAlg}(\mathbf{\Sigma})\to\mathsf{mCatAlg}(\mathbf{\Sigma})$;
   - gate: in both bags, the cells of dimension $>m$ fade.
3. Discretization:
   - derivor $\mathbf{Ds}^{(n,m)}\colon\mathbf{\Sigma}^{(n)}\to\mathbf{\Sigma}^{(m)}$, where $\mathrm{sc}^{k}_{s},\mathrm{tg}^{k}_{s},\circ^{k}_{s}\mapsto v^{s}_{0}$ for $m\le k<n$, the other symbols go to themselves, and the domains are empty;
   - a 1-cell gains an identity 2-cell (dashed);
   - $v^{s}_{0}\circ^{k}_{s}v^{s}_{1}$ is defined $\iff v^{s}_{0}=v^{s}_{1}$, "imposed by the domain conditions alone" (the obstacle of Scene 10, now solved).
4. The adjunction as a bijection of homomorphisms: $\mathsf{nCatAlg}(\mathbf{\Sigma})(\mathrm{Ds}^{(n,m)}(\calg{A}),\calg{B})\cong\mathsf{mCatAlg}(\mathbf{\Sigma})(\calg{A},\mathrm{Tr}^{(m,n)}(\calg{B}))$. On screen, an arrow from $\mathrm{Ds}^{(n,m)}(\calg{A})$ to $\calg{B}$ turns into an arrow from $\calg{A}$ to $\mathrm{Tr}^{(m,n)}(\calg{B})$.
5. Results:
   - $\mathrm{Tr}^{(m,n)}\circ\mathrm{Ds}^{(n,m)}=\mathrm{Id}$;
   - $\mathrm{Ds}^{(n,m)}\dashv\mathrm{Tr}^{(m,n)}$, unit $\mathrm{id}$, counit the inclusion of the $m$-cells;
   - in small type, "the same for $\mathrm{Ds}^{\mathrm{htg}(n,m)}\dashv\mathrm{Tr}^{\mathrm{htg}(m,n)}$".

**Voice-over.**
> Truncation from n to m is induced by the inclusion of the extension of dimension m into that of dimension n, with the domain: v zero equals its m-source, which keeps only the m-cells. Discretization goes the other way. It interprets the sources, targets and compositions of the dimensions from m up to n by a variable, and the domain conditions alone make two cells composable only when they are equal. These two functors are not inverse to each other, since truncation forgets the higher cells. But they form an adjunction: a homomorphism from a discretized algebra to an n-dimensional algebra is the same as a homomorphism into its truncation. So discretization is left adjoint to truncation, and truncating what was just discretized changes nothing. The same holds in the heterogeneous presentation.

## Scene 16 — The algebraic square

**Visuals.**
1. The definition, on a generic square:
   - categories $\mathsf{C},\mathsf{D}$ (top) and $\mathsf{C}',\mathsf{D}'$ (bottom);
   - adjunctions $F\dashv G$, $F'\dashv G'$ (horizontal) and $J\dashv K$, $H\dashv I$ (vertical);
   - the left adjoints commute up to $\alpha\colon F'\circ J\cong H\circ F$, the right adjoints up to $\beta\colon G\circ I\cong K\circ G'$.

   The generic letters then morph into the four functors (`TransformMatchingTex`).
2. The square of Scene 8 comes back, now with the adjunction symbols (⊥ between Gd and Uf, ⊢ between Tr and Ds, as in the paper's figure) and the $\mathrm{htg}$ labels on the right side.
3. Paths flash: $\mathrm{Gd}^{(n)}\circ\mathrm{Ds}^{(n,m)}=\mathrm{Ds}^{\mathrm{htg}(n,m)}\circ\mathrm{Gd}^{(m)}$.
4. Paths flash: $\beta^{(m,n)}\colon\mathrm{Uf}^{(m)}\circ\mathrm{Tr}^{\mathrm{htg}(m,n)}\cong\mathrm{Tr}^{(m,n)}\circ\mathrm{Uf}^{(n)}$.
5. Centre: "an algebraic square", with $\alpha=\mathrm{id}$ and $\beta=\beta^{(m,n)}$.

**Voice-over.**
> These adjunctions fit together. An algebraic square is made of four adjunctions arranged in a square, such that the left adjoints commute up to a natural isomorphism, and so do the right adjoints. Here, discretizing and then graduating is exactly the same as graduating and then discretizing in the heterogeneous presentation. And unifying and truncating, in either order, agree up to a natural isomorphism.

## Scene 17 — Dimension omega

**Visuals.**
1. The tower grows: $\omega\mathsf{CatAlg}(\mathbf{\Sigma})$ at the top, with projections $\mathrm{Tr}^{(n,\omega)}$.
2. The universal property: a category $\mathsf{L}$, functors $F_n$ with $F_m=\mathrm{Tr}^{(m,n)}\circ F_n$, and a unique $\langle F_k\rangle_{k\in\omega}$. Then:
   - $\omega\mathsf{CatAlg}(\mathbf{\Sigma})\cong\varprojlim_{n}\mathsf{nCatAlg}(\mathbf{\Sigma})$;
   - $\omega\mathsf{Cat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})\cong\varprojlim_{n}\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})$.
3. Notes:
   - teal: "$\mathrm{Tr}^{(n,\omega)}$, $\mathrm{Ds}^{(\omega,m)}$: induced by generalized hep-derivors";
   - orange: "$\mathrm{Gd}^{(\omega)}$: from the universal property".
4. "If $S\neq\varnothing$":
   - columns of cells $g_0, g_1, g_2,\dots$, where $g_k$ is a $(k+1)$-cell but not a $k$-cell (a 1-cell, a 2-globe, a 3-cell, …);
   - $g=(g_k)_{k\in\omega}$ in the product "has no finite dimension";
   - "homogeneous: $\omega\mathsf{CatAlg}(\mathbf{\Sigma})$ is **not** defined by QE-equations";
   - "heterogeneous: $\omega\mathsf{Cat}^{\mathrm{htg}}\mathsf{Alg}(\mathbf{\Sigma})=\mathsf{EPAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{\mathrm{htg}(\omega)}})$".

**Voice-over.**
> In dimension omega, the categories of omega-categorial algebras, in both presentations, are projective limits of their finite truncations: an omega-dimensional algebra is the same as a compatible family of finite ones. Truncation and discretization to and from omega are still induced by generalized hep-derivors, and graduation follows from the universal property of the limit. But the two presentations now behave differently. When there is at least one sort, the homogeneous omega-categorial algebras are not defined by QE-equations, because a product of cells of ever higher dimension has no finite dimension. The heterogeneous ones still are.

## Scene 18 — Unification in dimension omega

**Visuals.**
1. The grid with infinitely many rows ($k\in\omega$, a vertical ⋮), columns $s$ and $t$. "If $S\neq\varnothing$": a teal box picks one drawer, $A_{\varphi(s)}$, with the caption "a generalized hep-derivor takes the cells of $s$ from one carrier". Red cross.
2. For each sort, the quotient $[B]_s=\coprod_{k\in\omega}B_{(k,s)}/\Theta_s$:
   - the cells of column $s$ fly into a bag $[B]_s$;
   - each cell $x$ is linked by grey lines to its identities $\mathrm{i}^{(k,j)}_{s}(x)$, giving one class $[x]_j$;
   - the same for $t$.
3. $\mathrm{Gd}^{(\omega)}\dashv\mathrm{Uf}^{(\omega)}$, an adjoint equivalence; the square between $m$ and $\omega$.
4. **Recap of Part IV** (small card): "presentation: an equivalence; dimension: an adjunction; together: algebraic squares; ω: limits and one quotient".

**Voice-over.**
> Unification is different too. When there is at least one sort, no generalized hep-derivor can produce it: a derivor takes all the cells of a sort from a single carrier, but an omega-dimensional cell may come from any drawer. Instead, for every sort, we take the cells of all dimensions and glue each cell to its identities. With it, graduation and unification are again an adjoint equivalence, and the algebraic square holds between a finite dimension and omega.

## Part V — Signatures

## Scene 19 — Change of signature

**Visuals.**
1. A derivor $\mathbf{c}=(\varphi,c)\colon\mathbf{\Sigma}\to\mathbf{\Lambda}$ in $\mathsf{Sig}_{\mathfrak{d}}$. The sort chips $s,t$ of $\mathbf{\Sigma}$ both go to a single sort $u$ of $\mathbf{\Lambda}$: "$\varphi\colon S\to T$ may identify sorts".
2. The categorial extensions:
   - $\mathbf{c}^{(n)}\colon\mathbf{\Sigma}^{(n)}\to\mathbf{\Lambda}^{(n)}$, with $\mathrm{sc}^{k}_{s}\mapsto\mathrm{sc}^{k}_{\varphi(s)}(v^{\varphi(s)}_{0})$ and empty domains;
   - $\mathbf{c}^{\mathrm{htg}(n)}\colon\mathbf{\Sigma}^{\mathrm{htg}(n)}\to\mathbf{\Lambda}^{\mathrm{htg}(n)}$, with $\varphi^{\mathrm{htg}(n)}(k,s)=(k,\varphi(s))$: the columns $s$ and $t$ of the grid go to the column $u$.
3. Two levels: the functor $\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\colon\mathsf{nCatAlg}(\mathbf{\Lambda})\to\mathsf{nCatAlg}(\mathbf{\Sigma})$ goes backwards. "Split $\mathsf{Sig}_{\mathfrak{d}}$-indexed categories $\mathsf{nCatAlg}$, $\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}$".
4. A commuting square:
   - top: $\mathrm{Gd}^{(n)}_{\mathbf{\Lambda}}$; bottom: $\mathrm{Gd}^{(n)}_{\mathbf{\Sigma}}$; sides: $\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}$ and $\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}$;
   - from $\mathbf{c}^{(n)}\circ\mathbf{Gd}^{(n)}_{\mathbf{\Sigma}}=\mathbf{Gd}^{(n)}_{\mathbf{\Lambda}}\circ\mathbf{c}^{\mathrm{htg}(n)}$;
   - "the same for $\mathrm{Uf}^{(n)}$, $\mathrm{Ds}^{(n,m)}$, $\mathrm{Tr}^{(m,n)}$, their heterogeneous versions, and in dimension $\omega$".
5. "natural transformations between split indexed categories; they extend to the Grothendieck constructions".

**Voice-over.**
> Finally, the signature itself can change. A derivor from Sigma to Lambda may even identify sorts, for instance by sending both s and t to a single sort. It determines generalized hep-derivors between the categorial extensions, in every dimension and in both presentations, and they turn categorial Lambda-algebras into categorial Sigma-algebras. These functors form split indexed categories over the category of signatures and derivors: a category of algebras for every signature, and a functor for every derivor, compatible with composition. Graduation, unification, discretization and truncation all commute with them. So they are natural transformations between indexed categories, and they extend to the Grothendieck constructions, which gather the algebras of all signatures in a single category.

## Scene 20 — Summary and closing

**Visuals.**
1. The summary cube, the same one glimpsed in Scene 1, built in three steps from the square of Scene 16:
   - front face: $\mathbf{\Sigma}$, dimensions $m,n,\omega$, homogeneous and heterogeneous;
   - back face: $\mathbf{\Lambda}$, in grey;
   - arrows in depth: $\mathbf{c}^{(k)\ast}_{\mathfrak{gd}}$, $\mathbf{c}^{\mathrm{htg}(k)\ast}_{\mathfrak{gd}}$.
2. The three directions light up in turn: horizontal (presentation), vertical (dimension), depth (signature).
3. Every arrow except $\mathrm{Uf}^{(\omega)}$ turns teal: "generalized hep-derivors".
4. Title and authors; fade to black.

**Voice-over.**
> Here is the whole picture. Horizontal arrows change the presentation, vertical arrows change the dimension, and arrows in depth change the signature. All of them, except unification in dimension omega, come from one mechanism: generalized hep-derivors.
