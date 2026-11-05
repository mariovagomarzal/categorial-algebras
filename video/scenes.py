"""Higher-order many-sorted categorial algebras via generalized hep-derivors — video.

One Manim scene per scene of script.md. Every formula follows notation.py.
Render a scene with: uv run python -m manim -ql scenes.py Scene06SingleSetExtension
Build the whole video with: ./build.sh
"""

from components import *
import notation as N

TITLE = r"Higher-order many-sorted categorial algebras"
SUBTITLE = r"via generalized hep-derivors"
AUTHORS = r"J. Climent Vidal \quad E. Cosme Llópez \quad R. Ruiz Mora \quad M. Vago Marzal"
S_, T_ = SORT_COLORS["s"], SORT_COLORS["t"]
SIG = N.sig()
LAM = N.sig(r"\Lambda")
BB = r"\mathbf{B}"


class V3Scene(VoiceScene):
    part = 0
    show_progress = True

    def setup(self):
        super().setup()
        if self.show_progress:
            self.add(progress_bar(self.part))

    def head(self, text):
        h = heading(text)
        self.play(Write(h), run_time=0.8)
        return h


def title_block(scale=1.0):
    title = Tex(TITLE).scale(1.05 * scale)
    sub = Tex(SUBTITLE, color=DERIV_COLOR).scale(0.85 * scale).next_to(title, DOWN, buff=0.25)
    return VGroup(title, sub)


def globe(p, q, f="f", g="g", alpha=r"\alpha", bend=TAU / 7, labels=True):
    X = Dot(p, radius=0.07)
    Y = Dot(q, radius=0.07)
    top = mor(p, q, f if labels else None, angle=-bend, label_dir=UP)
    bot = mor(p, q, g if labels else None, angle=bend, label_dir=DOWN)
    cell = two_cell(top, bot, alpha if labels else None)
    return VGroup(X, Y, top, bot, cell)


# ---------------------------------------------------------------------------------------------
# Summary cube (Scenes 1 and 20)
# ---------------------------------------------------------------------------------------------

def summary_cube():
    """The summary figure of the paper: front face for Σ, back face for Λ, arrows in depth."""
    rows = [("m", 2.0), ("n", -0.1), ("omega", -2.2)]
    xs = [-3.9, 1.3]
    shift = np.array([1.5, 0.75, 0])
    front, back = {}, {}
    for d, y in rows:
        for col in range(2):
            p = np.array([xs[col], y, 0])
            front[(d, col)] = MathTex(N.cat(d, htg=bool(col))).scale(0.55).move_to(p)
            front[(d, col)].add_background_rectangle(opacity=1, buff=0.05)
            back[(d, col)] = MathTex(N.cat(d, htg=bool(col), s=N.sig(r"\Lambda")), color=GREY_C).scale(0.45).move_to(p + shift)

    def pair(a, b, horizontal, color=FUNCTOR_COLOR, width=3):
        side = UP if horizontal else RIGHT
        s = a.get_right() + RIGHT * 0.1 if horizontal else a.get_bottom() + DOWN * 0.08
        e = b.get_left() + LEFT * 0.1 if horizontal else b.get_top() + UP * 0.08
        kw = dict(buff=0, color=color, stroke_width=width, max_tip_length_to_length_ratio=0.06)
        return VGroup(Arrow(s + side * 0.09, e + side * 0.09, **kw), Arrow(e - side * 0.09, s - side * 0.09, **kw))

    horiz, vert, depth, back_arrows = VGroup(), VGroup(), VGroup(), VGroup()
    for d, _ in rows:
        horiz.add(pair(front[(d, 0)], front[(d, 1)], True))
        back_arrows.add(pair(back[(d, 0)], back[(d, 1)], True, GREY_D, 2))
    for (d1, _), (d2, _) in zip(rows, rows[1:]):
        for col in range(2):
            vert.add(pair(front[(d1, col)], front[(d2, col)], False))
            back_arrows.add(pair(back[(d1, col)], back[(d2, col)], False, GREY_D, 2))
    for key in front:
        depth.add(DashedLine(back[key].get_bottom(), front[key].get_top(), buff=0.06, color=DERIV_COLOR,
                             stroke_width=2.5, dash_length=0.07).add_tip(tip_length=0.12))
    return VGroup(*front.values()), VGroup(*back.values()), horiz, vert, depth, back_arrows


# ---------------------------------------------------------------------------------------------
# Part I — Algebras
# ---------------------------------------------------------------------------------------------

class Scene01Opening(V3Scene):
    scene_id = 1
    part = 0
    show_progress = False

    def construct(self):
        block = title_block()
        authors = Tex(AUTHORS).scale(0.5).next_to(block, DOWN, buff=0.5)
        self.play(Write(block[0]), run_time=1.2)
        self.play(FadeIn(block[1], shift=UP * 0.2), FadeIn(authors), run_time=0.8)

        # Map of the video: the summary cube, faded.
        self.cue(1, -0.4)
        cube = VGroup(*summary_cube()).scale(0.55).set_opacity(0.7).move_to(DOWN * 0.3)
        cap = T(r"by the end, we will read this picture", 0.65, YELLOW).to_edge(DOWN, buff=0.4)
        self.play(FadeOut(authors), block.animate.scale(0.5).to_edge(UP, buff=0.25), FadeIn(cube), FadeIn(cap), run_time=1.0)
        # Left: cells of every dimension.
        self.cue(1, 2.5)
        self.play(FadeOut(cube), FadeOut(cap), run_time=0.6)
        g = globe(LEFT * 5.2 + UP * 0.3, LEFT * 2.6 + UP * 0.3)
        trip = MathTex(r"\Rrightarrow", color=DIM3_COLOR).next_to(g, RIGHT, buff=0.2)
        lab1 = T(r"cells of every dimension", 0.6).next_to(g, DOWN, buff=0.6)
        self.play(Create(g), run_time=1.2)
        self.play(FadeIn(trip), FadeIn(lab1), run_time=0.6)

        # Right: several sorts and operations between them.
        self.cue(2)
        As = Ellipse(width=2.0, height=1.5, color=S_).set_fill(S_, 0.15).move_to(RIGHT * 1.6 + UP * 0.3)
        At = Ellipse(width=2.0, height=1.5, color=T_).set_fill(T_, 0.15).move_to(RIGHT * 4.6 + UP * 0.3)
        las = MathTex("A_s", color=S_).scale(0.7).next_to(As, UP, buff=0.05)
        lat = MathTex("A_t", color=T_).scale(0.7).next_to(At, UP, buff=0.05)
        pts = VGroup(*[Dot(As.get_center() + np.array([x, y, 0]), radius=0.05) for x, y in [(-0.5, 0.2), (0.3, -0.3), (0.4, 0.35)]],
                     *[Dot(At.get_center() + np.array([x, y, 0]), radius=0.05) for x, y in [(-0.4, -0.2), (0.35, 0.25)]])
        box = op_box(r"\sigma", size=0.7).move_to(RIGHT * 3.1 + DOWN * 1.3)
        a1 = Arrow(pts[0].get_center(), box.get_left(), buff=0.1, color=OP_COLOR, stroke_width=3)
        a2 = Arrow(pts[3].get_center(), box.get_right(), buff=0.1, color=OP_COLOR, stroke_width=3)
        lab2 = T(r"several sorts, operations between them", 0.6).next_to(box, DOWN, buff=0.3)
        self.play(FadeIn(As), FadeIn(At), FadeIn(las), FadeIn(lat), FadeIn(pts), run_time=1.0)
        self.play(FadeIn(box), GrowArrow(a1), GrowArrow(a2), FadeIn(lab2), run_time=1.0)

        # Both together.
        self.cue(3)
        g2 = globe(As.get_center() + LEFT * 0.6, As.get_center() + RIGHT * 0.6, labels=False, bend=TAU / 6)
        g3 = globe(At.get_center() + LEFT * 0.6, At.get_center() + RIGHT * 0.6, labels=False, bend=TAU / 6)
        self.play(FadeOut(pts), FadeOut(a1), FadeOut(a2), FadeOut(lab1), FadeOut(lab2), FadeOut(trip),
                  ReplacementTransform(g.copy(), g2), ReplacementTransform(g, g3), run_time=1.4)
        b1 = Arrow(g2.get_bottom(), box.get_left(), buff=0.1, color=OP_COLOR, stroke_width=3)
        b2 = Arrow(g3.get_bottom(), box.get_right(), buff=0.1, color=OP_COLOR, stroke_width=3)
        lab3 = T(r"$\sigma$ acts on cells", 0.6, OP_COLOR).next_to(box, DOWN, buff=0.3)
        self.play(GrowArrow(b1), GrowArrow(b2), FadeIn(lab3), run_time=0.9)

        self.cue(4, -0.2)
        big = title_block()
        self.play(FadeOut(VGroup(As, At, las, lat, g2, g3, box, b1, b2, lab3)), ReplacementTransform(block, big), run_time=1.2)
        self.cue(5, -0.1)
        self.play(Circumscribe(big[1], color=DERIV_COLOR, time_width=0.5), run_time=1.4)
        self.finish()


class Scene02Signatures(V3Scene):
    scene_id = 2
    part = 0

    def construct(self):
        self.head(r"Many-sorted signatures")
        sig = MathTex(SIG, "=", "(S,", r"\Sigma", ")").scale(0.9).move_to(LEFT * 3.8 + UP * 2.0)
        S = MathTex("S", "=", r"\{", "s", ",", "t", r"\}").scale(0.85).next_to(sig, DOWN, buff=0.35)
        S[3].set_color(S_)
        S[5].set_color(T_)
        rank = M(r"\sigma\in\Sigma_{\mathbf{s},s}\quad\mathbf{s}\in S^{\star}", 0.7).next_to(S, DOWN, buff=0.35)
        self.play(Write(sig), run_time=1.0)
        self.play(Write(S), run_time=0.9)
        self.play(FadeIn(rank), run_time=0.8)

        self.cue(1)
        r1 = MathTex(r"\sigma", r"\in", r"\Sigma_{(", "s", ",", "t", "),", "s", "}").scale(0.85)
        r2 = MathTex(r"\tau", r"\in", r"\Sigma_{(", "s", "),", "t", "}").scale(0.85)
        for r, cols in [(r1, {3: S_, 5: T_, 7: S_}), (r2, {3: S_, 5: T_})]:
            for i, c in cols.items():
                r[i].set_color(c)
            r[0].set_color(OP_COLOR)
        VGroup(r1, r2).arrange(DOWN, aligned_edge=LEFT, buff=0.35).next_to(rank, DOWN, buff=0.5)
        self.play(Write(r1), run_time=1.0)
        self.cue(2)
        self.play(Write(r2), run_time=0.9)

        self.cue(3)
        As = Ellipse(width=2.6, height=2.0, color=S_).set_fill(S_, 0.15).move_to(RIGHT * 1.2 + UP * 0.6)
        At = Ellipse(width=2.6, height=2.0, color=T_).set_fill(T_, 0.15).move_to(RIGHT * 4.6 + UP * 0.6)
        las = MathTex("A_s", color=S_).scale(0.75).next_to(As, UP, buff=0.05)
        lat = MathTex("A_t", color=T_).scale(0.75).next_to(At, UP, buff=0.05)
        A = MathTex(r"\mathbf{A}=(A,F),\quad A=(A_s,A_t)").scale(0.7).move_to(RIGHT * 2.9 + UP * 2.4)
        ps = [As.get_center() + np.array(v) for v in [(-0.7, 0.3, 0), (0.0, 0.5, 0), (0.6, 0.1, 0), (-0.3, -0.4, 0), (0.5, -0.5, 0)]]
        pt = [At.get_center() + np.array(v) for v in [(-0.6, 0.2, 0), (0.2, 0.5, 0), (0.6, -0.2, 0), (-0.2, -0.5, 0)]]
        ds = VGroup(*[Dot(p, radius=0.06) for p in ps])
        dt = VGroup(*[Dot(p, radius=0.06) for p in pt])
        self.play(FadeIn(As), FadeIn(At), FadeIn(las), FadeIn(lat), FadeIn(ds), FadeIn(dt), FadeIn(A), run_time=1.2)

        self.cue(4)
        box = op_box(r"\sigma", size=0.7).move_to(RIGHT * 2.9 + DOWN * 1.4)
        e1, e2 = ds[0].copy().set_color(YELLOW), dt[0].copy().set_color(YELLOW)
        self.play(FadeIn(box), e1.animate.move_to(box.get_center()), e2.animate.move_to(box.get_center()), run_time=1.0)
        self.remove(e1, e2)
        out = Dot(box.get_center(), radius=0.07, color=OP_COLOR)
        self.play(out.animate.move_to(ds[3].get_center() + RIGHT * 0.35), run_time=0.8)
        fs = M(r"\sigma^{\mathbf{A}}\colon A_s\times A_t\to A_s", 0.7).next_to(box, RIGHT, buff=0.5)
        self.play(Write(fs), run_time=1.0)
        self.cue(4, 6.0)
        tau = CurvedArrow(ds[2].get_center(), dt[2].get_center(), angle=-PI / 3, color=OP_COLOR, stroke_width=3, tip_length=0.15)
        ft = M(r"\tau^{\mathbf{A}}\colon A_s\to A_t", 0.7).next_to(fs, DOWN, buff=0.25, aligned_edge=LEFT)
        self.play(Create(tau), Write(ft), run_time=1.2)

        self.cue(5)
        fsp = M(r"\sigma^{\mathbf{A}}\colon A_s\times A_t\dashrightarrow A_s", 0.7).move_to(fs, aligned_edge=LEFT)
        self.play(Transform(fs, fsp), run_time=0.8)
        e1, e2 = ds[1].copy().set_color(YELLOW), dt[3].copy().set_color(YELLOW)
        self.play(e1.animate.move_to(box.get_left()), e2.animate.move_to(box.get_right()), run_time=0.7)
        cross = Cross(box, stroke_color=RED, stroke_width=5).scale(0.8)
        self.play(Create(cross), Wiggle(box), run_time=0.8)
        cats = M(r"\mathsf{Alg}(\Sigma)\subseteq\mathsf{PAlg}(\Sigma)", 0.7).next_to(r2, DOWN, buff=0.6, aligned_edge=LEFT)
        self.play(FadeOut(e1), FadeOut(e2), Write(cats), run_time=1.0)
        self.finish()


class Scene03CategoryAsPartialAlgebra(V3Scene):
    scene_id = 3
    part = 0

    def construct(self):
        self.head(r"A category is a partial algebra")

        self.cue(1)
        y = 1.0
        px, py, pz = np.array([-4.5, y, 0]), np.array([-2.0, y, 0]), np.array([0.5, y, 0])
        X, Y, Z = obj("X", px), obj("Y", py), obj("Z", pz)
        f = mor(px, py, "f")
        g = mor(py, pz, "g")
        self.play(LaggedStart(FadeIn(X), Create(f), FadeIn(Y), Create(g), FadeIn(Z), lag_ratio=0.3), run_time=1.6)

        self.cue(3)
        mid = f[0].point_from_proportion(0.5) + DOWN * 0.15
        sc_arrow = DashedLine(mid, px + DOWN * 0.9 + RIGHT * 0.1, color=GREY_B).add_tip(tip_length=0.15)
        tg_arrow = DashedLine(mid, py + DOWN * 0.9 + LEFT * 0.1, color=GREY_B).add_tip(tip_length=0.15)
        sc_lab = M(r"\mathrm{sc}(f)", 0.65, GREY_B).next_to(sc_arrow.get_end(), DOWN, buff=0.1)
        tg_lab = M(r"\mathrm{tg}(f)", 0.65, GREY_B).next_to(tg_arrow.get_end(), DOWN, buff=0.1)
        self.play(X[1].animate.next_to(X[0], UP, buff=0.15), Y[1].animate.next_to(Y[0], UP, buff=0.15),
                  Z[1].animate.next_to(Z[0], UP, buff=0.15), run_time=0.5)
        self.play(Create(sc_arrow), Create(tg_arrow), FadeIn(sc_lab), FadeIn(tg_lab), run_time=1.0)

        self.cue(4)
        loops = VGroup()
        for p, name in [(px, "X"), (py, "Y"), (pz, "Z")]:
            loop = CurvedArrow(p + LEFT * 0.12 + UP * 0.1, p + RIGHT * 0.12 + UP * 0.1, angle=-1.6 * PI,
                               color=ID_COLOR, stroke_width=3, tip_length=0.13)
            lab = MathTex(rf"\mathrm{{id}}_{name}", color=ID_COLOR).scale(0.6).next_to(loop, UP, buff=0.05)
            loops.add(VGroup(loop, lab))
        self.play(*[ReplacementTransform(o[1], l) for o, l in zip([X, Y, Z], loops)], run_time=1.0)
        self.play(sc_lab.animate.become(M(r"\mathrm{sc}(f)=\mathrm{id}_X", 0.65, GREY_B).move_to(sc_lab).shift(LEFT * 0.3)),
                  tg_lab.animate.become(M(r"\mathrm{tg}(f)=\mathrm{id}_Y", 0.65, GREY_B).move_to(tg_lab).shift(RIGHT * 0.3)),
                  run_time=0.8)
        sack = bag(3.6, 2.2, "C").move_to(RIGHT * 4.3 + UP * 0.6)
        names = [r"f", r"g", r"\mathrm{id}_X", r"\mathrm{id}_Y", r"\mathrm{id}_Z"]
        spots = [[-0.9, 0.35], [0.6, 0.5], [-0.3, -0.45], [0.9, -0.3], [-1.1, -0.15]]
        items = VGroup(*[MathTex(n, color=DIM_COLORS[1] if i < 2 else ID_COLOR).scale(0.7).move_to(sack[0].get_center() + np.array([sx, sy, 0]))
                         for i, (n, (sx, sy)) in enumerate(zip(names, spots))])
        cap = T(r"homogeneous category", 0.6, BAG_COLOR).next_to(sack, DOWN, buff=0.15)
        self.play(FadeIn(sack), FadeIn(cap), LaggedStart(*[TransformFromCopy(s, t) for s, t in
                  zip([f[1], g[1], loops[0][1], loops[1][1], loops[2][1]], items)], lag_ratio=0.15), run_time=1.6)

        self.cue(5)
        diagram = VGroup(X[0], Y[0], Z[0], f, g, loops, sc_arrow, tg_arrow, sc_lab, tg_lab)
        self.play(FadeOut(diagram), FadeOut(cap), VGroup(sack, items).animate.scale(0.8).move_to(LEFT * 4.8 + DOWN * 0.3), run_time=1.0)
        comp = MathTex(r"g \circ f", r"\text{ is defined}", r"\iff", r"\mathrm{sc}(g)", N.EEQ, r"\mathrm{tg}(f)").scale(0.85)
        comp.move_to(RIGHT * 1.2 + UP * 1.6)
        self.play(Write(comp[:2]), run_time=0.9)

        self.cue(6)
        self.play(Write(comp[2:]), run_time=1.4)
        self.play(Indicate(comp[3:], color=YELLOW), run_time=1.0)

        self.cue(7)
        eq_lab = T(r"existence equation", 0.6, YELLOW).next_to(comp[4], DOWN, buff=0.25)
        self.play(FadeIn(eq_lab, shift=UP * 0.1), comp[4].animate.set_color(YELLOW), run_time=0.9)

        self.cue(8)
        laws = VGroup(
            M(r"\mathrm{sc}(\mathrm{sc}(f)) = \mathrm{sc}(f)", 0.65),
            M(r"f \circ \mathrm{sc}(f) = f \qquad \mathrm{tg}(f) \circ f = f", 0.65),
            M(r"h \circ (g \circ f) = (h \circ g) \circ f", 0.65),
        ).arrange(DOWN, buff=0.22).next_to(eq_lab, DOWN, buff=0.4)
        self.play(LaggedStartMap(FadeIn, laws, shift=RIGHT * 0.2, lag_ratio=0.3), run_time=1.6)
        frame = SurroundingRectangle(VGroup(comp, eq_lab, laws), color=OP_COLOR, buff=0.25)
        tag = T(r"QE-equations", 0.75, OP_COLOR).next_to(frame, DOWN, buff=0.15)
        self.play(Create(frame), Write(tag), run_time=1.1)
        self.finish()


class Scene04SingleSetNCategories(V3Scene):
    scene_id = 4
    part = 0

    def construct(self):
        self.head(r"Homogeneous $n$-categories")
        C = M(r"\mathsf{C}=(C,(\xi_k)_{k\in n}),\qquad \xi_k=(\circ^{k},\mathrm{sc}^{k},\mathrm{tg}^{k})", 0.75).move_to(UP * 2.4)
        self.play(Write(C), run_time=1.6)
        sack = Ellipse(width=4.2, height=2.6, color=BAG_COLOR).set_fill(BAG_COLOR, 0.12).move_to(LEFT * 3.4 + DOWN * 0.3)
        layers = VGroup(*[Ellipse(width=4.2 - 0.5 * i, height=2.6 - 0.35 * i, color=DIM_COLORS[min(i + 1, 2)], stroke_opacity=0.6)
                          .move_to(sack) for i in range(2)])
        lab = MathTex("C", color=BAG_COLOR).scale(0.75).next_to(sack, UP, buff=0.05)
        g = globe(sack.get_center() + LEFT * 1.0, sack.get_center() + RIGHT * 1.0, f="f", g="f'")
        self.play(FadeIn(sack), FadeIn(lab), Create(layers), run_time=1.2)
        self.play(Create(g), run_time=1.4)

        self.cue(1)
        kc = M(r"C_k=\{f\in C\mid f=\mathrm{sc}^{k}(f)\}", 0.75).move_to(RIGHT * 2.8 + UP * 1.2)
        self.play(Write(kc), run_time=1.2)
        self.play(Indicate(VGroup(g[0], g[1]), color=WHITE), Indicate(VGroup(g[2], g[3]), color=BLUE), run_time=1.2)

        self.cue(2)
        self.play(FadeOut(VGroup(sack, layers, lab, g)), kc.animate.scale(0.8).move_to(RIGHT * 3.6 + UP * 1.6), run_time=0.8)
        size = 1.2
        grid = VGroup()
        names = [["f", "g"], ["f'", "g'"]]
        for r in range(2):
            for c in range(2):
                sq = Square(size, color=DIM_COLORS[2]).set_fill(DIM_COLORS[2], 0.12)
                sq.move_to(np.array([(c - 0.5) * size, (0.5 - r) * size, 0]))
                grid.add(VGroup(sq, MathTex(names[r][c], color=DIM_COLORS[2]).move_to(sq)))
        grid.move_to(LEFT * 3.2 + UP * 0.2)
        jk = T(r"two dimensions $j<k$: compatible structures", 0.6).next_to(grid, DOWN, buff=0.4)
        self.play(LaggedStartMap(FadeIn, grid, lag_ratio=0.15), FadeIn(jk), run_time=1.0)

        self.cue(3)
        rows = VGroup(*[SurroundingRectangle(VGroup(grid[2 * r], grid[2 * r + 1]), color=DIM_COLORS[1], buff=0.06) for r in range(2)])
        cols = VGroup(*[SurroundingRectangle(VGroup(grid[c], grid[c + 2]), color=DIM_COLORS[1], buff=0.06) for c in range(2)])
        law = M(r"(g'\circ^{0}f')\circ^{1}(g\circ^{0}f)=(g'\circ^{1}g)\circ^{0}(f'\circ^{1}f)", 0.8).move_to(RIGHT * 2.2 + DOWN * 0.4)
        self.play(Create(rows), run_time=0.6)
        self.play(ReplacementTransform(rows, cols), run_time=0.8)
        self.play(FadeOut(cols), Write(law), run_time=1.6)

        self.cue(4)
        name = T(r"interchange law", 0.75, YELLOW).next_to(law, DOWN, buff=0.3)
        self.play(Write(name), Circumscribe(law, color=YELLOW), run_time=1.2)
        self.finish()


class Scene05CategorialAlgebras(V3Scene):
    scene_id = 5
    part = 0

    def construct(self):
        self.head(r"Many-sorted $n$-categorial algebras")
        As = sort_bag("s", r"\mathsf{A}_s", 2.4, 1.5).move_to(LEFT * 5.2 + UP * 1.5)
        At = sort_bag("t", r"\mathsf{A}_t", 2.4, 1.5).move_to(LEFT * 5.2 + DOWN * 0.7)
        A = M(r"\mathsf{A}=(\mathsf{A}_s)_{s\in S}", 0.7).next_to(At, DOWN, buff=0.25)
        self.play(FadeIn(As), FadeIn(At), FadeIn(A), run_time=1.2)
        box = op_box(r"\sigma", size=0.75).move_to(LEFT * 2.4 + UP * 0.4)
        out = sort_bag("s", r"\mathsf{A}_s", width=2.0, height=1.4, dims=(0, 1, 2)).move_to(LEFT * 0.2 + UP * 0.4)
        a1 = Arrow(As.get_right(), box.get_left(), buff=0.1, color=OP_COLOR, stroke_width=3)
        a2 = Arrow(At.get_right(), box.get_left(), buff=0.1, color=OP_COLOR, stroke_width=3)
        a3 = Arrow(box.get_right(), out.get_left(), buff=0.1, color=OP_COLOR, stroke_width=3)
        fs = M(r"\sigma^{\calg{A}}\colon\mathsf{A}_s\times\mathsf{A}_t\to\mathsf{A}_s", 0.7).move_to(RIGHT * 3.8 + UP * 2.0)
        ft = M(r"\tau^{\calg{A}}\colon\mathsf{A}_s\to\mathsf{A}_t", 0.7).next_to(fs, DOWN, buff=0.15)
        self.cue(0, 5.0)
        self.play(FadeIn(box), GrowArrow(a1), GrowArrow(a2), GrowArrow(a3), FadeIn(out), Write(fs), run_time=1.6)
        self.play(Write(ft), run_time=0.8)

        self.cue(1)
        law = VGroup(
            M(r"\sigma(g\circ^{k}f,\;b\circ^{k}a)=\sigma(g,b)\circ^{k}\sigma(f,a)", 0.7),
            M(r"\mathrm{sc}^{k}(\sigma(f,a))=\sigma(\mathrm{sc}^{k}(f),\mathrm{sc}^{k}(a))", 0.7),
        ).arrange(DOWN, buff=0.2).move_to(RIGHT * 3.6 + DOWN * 0.4)
        who = T(r"$f,g$ of sort $s$; $a,b$ of sort $t$", 0.6, GREY_A).next_to(law, UP, buff=0.2)
        self.play(FadeIn(who), Write(law[0]), run_time=1.6)
        self.play(Write(law[1]), run_time=1.2)
        cap = T(r"an $n$-functor on $\mathsf{A}_{(s,t)}=\mathsf{A}_s\times\mathsf{A}_t$, componentwise", 0.6, OP_COLOR).next_to(law, DOWN, buff=0.25)
        self.play(FadeIn(cap), run_time=0.7)

        self.cue(2)
        self.play(FadeOut(VGroup(As, At, A, box, out, a1, a2, a3, fs, ft, law, who, cap)), run_time=0.7)
        defn = Tex(r"a \textbf{many-sorted $n$-categorial $\mathbf{\Sigma}$-algebra}:\\",
                   r"a homogeneous $n$-category for each sort $+$ every operation symbol an $n$-functor").scale(0.65)
        dbox = framed(defn, OP_COLOR).move_to(UP * 1.9)
        zero = T(r"$n=0$: ordinary $\Sigma$-algebras", 0.65).next_to(dbox, DOWN, buff=0.3)
        self.play(FadeIn(dbox), run_time=0.8)
        self.play(FadeIn(zero), run_time=0.7)

        self.cue(3)
        A1 = sort_bag("s", r"\mathsf{A}_s", 1.8, 1.3, (0, 1, 2)).move_to(LEFT * 4.0 + DOWN * 0.4)
        A2 = sort_bag("t", r"\mathsf{A}_t", 1.8, 1.3, (0, 1, 2)).move_to(LEFT * 4.0 + DOWN * 2.2)
        B1 = sort_bag("s", r"\mathsf{B}_s", 1.8, 1.3, (0, 1, 2)).move_to(LEFT * 0.6 + DOWN * 0.4)
        B2 = sort_bag("t", r"\mathsf{B}_t", 1.8, 1.3, (0, 1, 2)).move_to(LEFT * 0.6 + DOWN * 2.2)
        H1 = Arrow(A1.get_right(), B1.get_left(), buff=0.1, color=FUNCTOR_COLOR, stroke_width=4)
        H2 = Arrow(A2.get_right(), B2.get_left(), buff=0.1, color=FUNCTOR_COLOR, stroke_width=4)
        h1 = MathTex("H_s", color=FUNCTOR_COLOR).scale(0.7).next_to(H1, UP, buff=0.05)
        h2 = MathTex("H_t", color=FUNCTOR_COLOR).scale(0.7).next_to(H2, UP, buff=0.05)
        self.play(FadeIn(VGroup(A1, A2, B1, B2)), run_time=0.8)
        self.play(GrowArrow(H1), GrowArrow(H2), FadeIn(h1), FadeIn(h2), run_time=0.9)
        hom = M(r"H_s(\sigma^{\calg{A}}(f,a))=\sigma^{\calg{B}}(H_s(f),H_t(a))", 0.7).move_to(RIGHT * 3.6 + DOWN * 0.05)
        self.play(Write(hom), run_time=1.4)

        self.cue(4)
        cat = M(N.cat(), 0.9).next_to(hom, DOWN, buff=0.3)
        self.play(Write(cat), run_time=0.9)
        rec = recap_card([r"signature $\mathbf{\Sigma}$ with sorts $s,t$", r"partial algebras",
                          r"homogeneous $n$-categories", r"$n$-categorial $\mathbf{\Sigma}$-algebras"], "Part I").to_corner(DR, buff=0.45).shift(UP * 0.35)
        self.wait(1.0)
        self.play(FadeIn(rec, shift=LEFT * 0.2), run_time=0.8)
        self.finish()


# ---------------------------------------------------------------------------------------------
# Part II — Presentations
# ---------------------------------------------------------------------------------------------

class Scene06SingleSetExtension(V3Scene):
    scene_id = 6
    part = 1

    def construct(self):
        self.head(r"The homogeneous categorial extension $\mathbf{\Sigma}^{(n)}$")
        base = VGroup(M(r"\sigma\colon(s,t)\to s", 0.7, OP_COLOR), M(r"\tau\colon(s)\to t", 0.7, OP_COLOR))
        base.arrange(DOWN, aligned_edge=LEFT, buff=0.2).move_to(LEFT * 4.6 + UP * 1.7)
        lab = M(r"\Sigma", 0.8).next_to(base, UP, buff=0.2)
        self.play(FadeIn(lab), FadeIn(base), run_time=0.8)

        self.cue(1)
        ext = M(N.ext(), 0.8).move_to(LEFT * 0.9 + UP * 2.35)
        rows = VGroup()
        for k, color in [(0, DIM_COLORS[1]), (1, DIM_COLORS[2])]:
            r = VGroup(M(rf"{N.sc(k, 's')},\ {N.tg(k, 's')}\colon(s)\to s\qquad {N.comp(k, 's')}\colon(s,s)\to s", 0.65, color),
                       M(rf"{N.sc(k, 't')},\ {N.tg(k, 't')}\colon(t)\to t\qquad {N.comp(k, 't')}\colon(t,t)\to t", 0.65, color))
            r.arrange(DOWN, aligned_edge=LEFT, buff=0.12)
            rows.add(r)
        dots = M(r"\vdots\qquad k=0,1,\dots,n-1", 0.65, GREY_B)
        rows.add(dots)
        rows.arrange(DOWN, aligned_edge=LEFT, buff=0.25).move_to(RIGHT * 1.6 + UP * 0.75)
        self.play(Write(ext), run_time=0.8)
        self.play(LaggedStartMap(FadeIn, rows, shift=DOWN * 0.15, lag_ratio=0.4), run_time=3.0)

        self.cue(2)
        dc = M(N.domain_condition(), 0.72, YELLOW).move_to(DOWN * 1.2)
        others = T(r"every other symbol: $\varnothing$", 0.6, GREY_A).next_to(dc, DOWN, buff=0.15)
        self.play(Write(dc), run_time=1.6)
        self.cue(3)
        self.play(Indicate(dc, color=YELLOW), FadeIn(others), run_time=1.2)

        self.cue(4)
        self.play(FadeOut(VGroup(base, lab, rows, others)), dc.animate.scale(0.85).move_to(UP * 1.6 + RIGHT * 2.0), ext.animate.move_to(LEFT * 4.6 + UP * 2.3), run_time=0.8)
        top = M(N.comp("k", "s"), 0.85).move_to(LEFT * 4.6 + UP * 1.0)
        bot = M(rf"{N.sc('k', 's')}\qquad {N.tg('k', 's')}", 0.75).move_to(LEFT * 4.6 + DOWN * 0.5)
        l1 = Arrow(top.get_bottom(), bot[0].get_top() + LEFT * 0.5, buff=0.1, color=GREY_B, stroke_width=3)
        l2 = Arrow(top.get_bottom(), bot[0].get_top() + RIGHT * 0.5, buff=0.1, color=GREY_B, stroke_width=3)
        lhd = MathTex(r"\lhd", color=GREY_B).scale(0.8).next_to(VGroup(l1, l2), LEFT, buff=0.1)
        self.play(FadeIn(top), FadeIn(bot), GrowArrow(l1), GrowArrow(l2), FadeIn(lhd), run_time=1.2)

        self.cue(5)
        hep = T(r"well-founded: a \textbf{hep-signature}\\(hierarchical equationally partial)", 0.6).next_to(bot, DOWN, buff=0.35)
        self.play(FadeIn(hep), run_time=0.9)

        self.cue(6)
        ep = M(r"\mathrm{Dom}(\sigma^{\mathbf{A}})=A_{\mathrm{def}(\sigma)}", 0.8).move_to(RIGHT * 2.0 + UP * 0.4)
        ep_lab = T(r"ep-algebra: defined \textbf{exactly} where the domain conditions hold", 0.6).next_to(ep, DOWN, buff=0.2)
        self.play(Write(ep), FadeIn(ep_lab), run_time=1.6)
        self.cue(7, -0.5)
        # The composable pairs light up: a small chain of arrows in sort s.
        p = [RIGHT * (0.2 + 1.3 * i) + DOWN * 1.6 for i in range(4)]
        chain = VGroup(*[Dot(q, radius=0.06) for q in p])
        arrs = VGroup(*[mor(p[i], p[i + 1], lab, color=DIM_COLORS[1]) for i, lab in enumerate(["f", "g", "h"])])
        self.play(FadeIn(chain), Create(arrs), run_time=0.9)
        ok = M(r"g\circ^{0}_{s}f\ \checkmark", 0.65, GREEN).next_to(arrs[0:2], DOWN, buff=0.25)
        self.play(Indicate(arrs[0], color=GREEN), Indicate(arrs[1], color=GREEN), FadeIn(ok), run_time=1.0)

        self.cue(8)
        res = framed(M(rf"{N.cat()}=\mathsf{{EPAlg}}(\boldsymbol{{\mathcal{{C}}}}^{{{N.ext()}}})", 0.8), OP_COLOR).move_to(DOWN * 2.85 + RIGHT * 0.6)
        qe = T(r"$\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}}$: QE-equations", 0.6, OP_COLOR).next_to(res, RIGHT, buff=0.3)
        self.play(FadeOut(VGroup(chain, arrs, ok)), FadeIn(res), FadeIn(qe), run_time=1.4)
        self.finish()


def glob_grid_labels(cols, carriers=False):
    labels = VGroup()
    for col in cols:
        for d in col:
            if carriers:
                labels.add(MathTex(rf"A_{{({d.k},{d.sort_name})}}", color=SORT_COLORS[d.sort_name]).scale(0.5).move_to(d[0].get_right() + LEFT * 0.4))
    return labels


class Scene07HeterogeneousExtension(V3Scene):
    scene_id = 7
    part = 1

    def construct(self):
        self.head(r"The heterogeneous categorial extension $\mathbf{\Sigma}^{\mathrm{htg}(n)}$")
        byd = T(r"heterogeneous: by dimension (not by sort)", 0.6, GREY_A).next_to(heading(""), DOWN, buff=0.55)
        self.play(FadeIn(byd), run_time=0.6)
        cols = drawer_grid(rows=3, top="n").move_to(LEFT * 3.2 + DOWN * 0.3)
        kl = VGroup(*[MathTex(f"k={k}" if k < 2 else "k=n", color=GREY_B).scale(0.55).next_to(cols[0][k], LEFT, buff=0.2) for k in range(3)])
        sl = VGroup(MathTex("s", color=S_).scale(0.7).next_to(cols[0], DOWN, buff=0.15),
                    MathTex("t", color=T_).scale(0.7).next_to(cols[1], DOWN, buff=0.15))
        self.cue(1)
        self.play(FadeOut(byd), LaggedStartMap(FadeIn, VGroup(*cols[0], *cols[1]), lag_ratio=0.08), FadeIn(kl), FadeIn(sl), run_time=1.6)
        srt = M(r"\text{sorts }(k,s)\in(n+1)\times S", 0.65).move_to(RIGHT * 2.6 + UP * 2.3)
        self.play(Write(srt), run_time=1.0)

        self.cue(3)
        cops = VGroup(M(r"\sigma_k\colon((k,s),(k,t))\to(k,s)", 0.7, OP_COLOR), M(r"\tau_k\colon((k,s))\to(k,t)", 0.7, OP_COLOR))
        cops.arrange(DOWN, aligned_edge=LEFT, buff=0.15).next_to(srt, DOWN, buff=0.35)
        rowarrs = VGroup(*[DoubleArrow(cols[0][k][0].get_right(), cols[1][k][0].get_left(), buff=0.03, color=OP_COLOR,
                                       stroke_width=2.5, tip_length=0.12) for k in range(3)])
        self.play(Write(cops), Create(rowarrs), run_time=1.6)

        self.cue(4)
        down = Arrow(cols[0][2][0].get_bottom() + LEFT * 0.5, cols[0][1][0].get_top() + LEFT * 0.5, buff=0.02, color=STRUCT_COLOR, stroke_width=3, max_tip_length_to_length_ratio=0.5)
        up = Arrow(cols[0][1][0].get_top() + RIGHT * 0.5, cols[0][2][0].get_bottom() + RIGHT * 0.5, buff=0.02, color=ID_COLOR, stroke_width=3, max_tip_length_to_length_ratio=0.5)
        struct = VGroup(M(rf"{N.gsc()},\ {N.gtg()}\ \downarrow\qquad {N.gid()}\ \uparrow", 0.65, STRUCT_COLOR),
                        M(rf"\mathrm{{def}}({N.gcomp()})=\{{{N.gsc()}(v^{{(k,s)}}_{{0}}){N.EEQ}{N.gtg()}(v^{{(k,s)}}_{{1}})\}}", 0.62, YELLOW))
        struct.arrange(DOWN, aligned_edge=LEFT, buff=0.2).next_to(cops, DOWN, buff=0.35, aligned_edge=LEFT)
        self.play(GrowArrow(down), GrowArrow(up), Write(struct[0]), run_time=1.4)
        self.play(Write(struct[1]), run_time=1.6)

        # A concrete algebra for n = 1.
        self.cue(5)
        self.play(FadeOut(VGroup(srt, cops, struct, down, up, rowarrs, kl, sl, cols)), run_time=0.6)
        g2 = drawer_grid(rows=2, width=2.6, height=0.8, label=False).move_to(UP * 1.3)
        carr = VGroup(*[MathTex(rf"A_{{({d.k},{d.sort_name})}}", color=SORT_COLORS[d.sort_name]).scale(0.55).next_to(d[0], LEFT if d.sort_name == "s" else RIGHT, buff=0.1)
                        for col in g2 for d in col])
        c00 = VGroup(MathTex("x").scale(0.7), MathTex("y").scale(0.7)).arrange(RIGHT, buff=0.7).move_to(g2[0][0])
        c10 = VGroup(MathTex(r"f\colon x\to y", color=BLUE).scale(0.6), MathTex(r"\mathrm{i}(x)", color=ID_COLOR).scale(0.55),
                     MathTex(r"\mathrm{i}(y)", color=ID_COLOR).scale(0.55)).arrange(RIGHT, buff=0.18).move_to(g2[0][1])
        c01 = MathTex("z").scale(0.7).move_to(g2[1][0])
        c11 = VGroup(MathTex(r"a\colon z\to z", color=BLUE).scale(0.6), MathTex(r"\mathrm{i}(z)", color=ID_COLOR).scale(0.55)).arrange(RIGHT, buff=0.2).move_to(g2[1][1])
        self.play(FadeIn(g2), FadeIn(carr), FadeIn(VGroup(c00, c10, c01, c11)), run_time=1.2)
        e1 = M(r"\sigma_1(f,a)\in A_{(1,s)}", 0.75, OP_COLOR).move_to(DOWN * 0.3)
        self.play(Indicate(c10[0]), Indicate(c11[0]), Write(e1), run_time=1.4)
        e2 = M(rf"{N.gsc(0, 1, 's')}(\sigma_1(f,a))=\sigma_0({N.gsc(0, 1, 's')}(f),{N.gsc(0, 1, 't')}(a))", 0.62).next_to(e1, DOWN, buff=0.35)
        e3 = M(r"=\sigma_0(x,z)\in A_{(0,s)}", 0.7).next_to(e2, RIGHT, buff=0.15)
        VGroup(e2, e3).move_to(DOWN * 1.05)
        self.cue(5, 5.0)
        self.play(Write(e2), run_time=1.8)
        self.play(Write(e3), run_time=1.0)

        self.cue(6)
        res = framed(M(rf"{N.cat(htg=True)}=\mathsf{{EPAlg}}(\boldsymbol{{\mathcal{{C}}}}^{{{N.ext(htg=True)}}})", 0.75), OP_COLOR).move_to(DOWN * 2.3)
        self.play(FadeIn(res), run_time=1.0)

        self.cue(7)
        self.play(FadeOut(VGroup(g2, carr, c00, c10, c01, c11, e1, e2, e3, res)), run_time=0.6)
        divider = DashedLine(UP * 2.5, DOWN * 2.6, color=GREY_D)
        As = sort_bag("s", r"\mathsf{A}_s", 1.9, 1.4).move_to(LEFT * 5.0 + UP * 0.4)
        At = sort_bag("t", r"\mathsf{A}_t", 1.9, 1.4).move_to(LEFT * 2.6 + UP * 0.4)
        gg = drawer_grid(rows=3, width=1.5, height=0.5, top="n").move_to(RIGHT * 3.6 + UP * 0.4)
        cl = M(N.cat(), 0.75, BAG_COLOR).move_to(LEFT * 3.8 + DOWN * 1.8)
        cr = M(N.cat(htg=True), 0.75, DRAWER_COLOR).move_to(RIGHT * 3.6 + DOWN * 1.8)
        self.play(Create(divider), FadeIn(As), FadeIn(At), FadeIn(gg), Write(cl), Write(cr), run_time=1.4)
        self.cue(8)
        q = MathTex(r"\overset{?}{\simeq}").scale(1.5).move_to(DOWN * 1.8)
        self.play(FadeIn(q, scale=0.5), run_time=0.6)
        self.finish()


def square_labels(m="m", n="n", w=3.4, h=1.5, center=UP * 0.4, scale=0.7):
    return cat_square(N.cat(m), N.cat(m, htg=True), N.cat(n), N.cat(n, htg=True), w=w, h=h, scale=scale, center=center)


def functor_square(labels, m="m", n="n", s=None, symbol=True, scale=0.6):
    return square_arrows(labels, gd=N.functor("Gd", m, s=s), uf=N.functor("Uf", m, s=s),
                         ds=N.functor("Ds", n, m, s=s), tr=N.functor("Tr", m, n, s=s), symbol=symbol, scale=scale)


def fix_square(top, bot, left, right, m="m", n="n", s=None, scale=0.6):
    """Bottom and right labels of a square: Gd^{(n)}, Uf^{(n)} and the heterogeneous Ds, Tr."""
    bot[2].become(MathTex(N.functor("Gd", n, s=s), color=FUNCTOR_COLOR).scale(scale).move_to(bot[2]))
    bot[3].become(MathTex(N.functor("Uf", n, s=s), color=FUNCTOR_COLOR).scale(scale).move_to(bot[3]))
    right[2].become(MathTex(N.functor("Ds", n, m, htg=True, s=s), color=FUNCTOR_COLOR).scale(scale).next_to(right[0], RIGHT, buff=0.08))
    right[3].become(MathTex(N.functor("Tr", m, n, htg=True, s=s), color=FUNCTOR_COLOR).scale(scale).next_to(right[1], LEFT, buff=0.08))


class Scene08FourFunctors(V3Scene):
    scene_id = 8
    part = 1

    def construct(self):
        self.head(r"Four functors, one mechanism?")
        labels = square_labels(center=UP * 0.15)
        top, bot, left, right = functor_square(labels, s=SIG, symbol=False)
        fix_square(top, bot, left, right, s=SIG)
        mn = T(r"$m\le n$", 0.6, GREY_A).next_to(labels, LEFT, buff=0.4)
        self.play(LaggedStartMap(FadeIn, labels, lag_ratio=0.15), FadeIn(mn), run_time=1.2)

        self.cue(1)
        pres = T(r"change the presentation", 0.6, FUNCTOR_COLOR).next_to(labels[:2], UP, buff=0.7)
        self.play(Create(top), Create(bot), FadeIn(pres), run_time=1.4)

        self.cue(2)
        dim = T(r"change\\the dimension", 0.6, FUNCTOR_COLOR).next_to(labels[0], LEFT, buff=0.5).shift(DOWN * 1.5)
        self.play(Create(left), Create(right), FadeOut(mn), FadeIn(dim), run_time=1.4)

        self.cue(3)
        note = framed(T(r"from now on we drop $\mathbf{\Sigma}$: $\mathrm{Gd}^{(n)}$, $\mathrm{Ds}^{(n,m)}$, \dots\\heterogeneous symbols carry $\mathrm{htg}$, homogeneous ones no marker", 0.6), GREY_B).to_edge(DOWN, buff=0.7)
        self.play(FadeIn(note), run_time=0.8)
        top2, bot2, left2, right2 = functor_square(labels, symbol=False)
        fix_square(top2, bot2, left2, right2)
        self.wait(1.2)
        self.play(*[ReplacementTransform(a[i], b[i]) for a, b in [(top, top2), (bot, bot2), (left, left2), (right, right2)] for i in (2, 3)], run_time=1.2)

        self.cue(4)
        rec = recap_card([r"two categorial extensions $\mathbf{\Sigma}^{(n)}$, $\mathbf{\Sigma}^{\mathrm{htg}(n)}$",
                          r"two categories of algebras", r"four functors"], "Part II").to_corner(DR, buff=0.4).shift(UP * 0.35)
        self.play(FadeOut(note), FadeIn(rec, shift=LEFT * 0.2), run_time=0.8)

        self.cue(5)
        q = T(r"one mechanism, for every signature?", 0.7).move_to(DOWN * 2.35 + LEFT * 1.5)
        self.play(FadeOut(rec), Write(q), run_time=1.2)

        self.cue(6)
        S = MathTex(SIG).move_to(RIGHT * 2.2 + DOWN * 2.35)
        L = MathTex(N.sig(r"\Lambda")).move_to(RIGHT * 4.4 + DOWN * 2.35)
        arr = DashedLine(S.get_right(), L.get_left(), buff=0.2, color=DERIV_COLOR).add_tip(tip_length=0.15)
        lab = T(r"a translation of signatures?", 0.6, DERIV_COLOR).next_to(VGroup(S, L), DOWN, buff=0.15)
        self.play(FadeIn(S), FadeIn(L), Create(arr), FadeIn(lab), run_time=1.0)
        self.finish()


# ---------------------------------------------------------------------------------------------
# Part III — Generalized hep-derivors
# ---------------------------------------------------------------------------------------------

class Scene09Derivors(V3Scene):
    scene_id = 9
    part = 2

    def construct(self):
        self.head(r"Derivors")
        d = M(rf"{N.derivor(generalized=False)}\colon{SIG}\to{LAM}", 0.8).move_to(UP * 2.3)
        phi = M(r"\varphi\colon S\to T", 0.75).next_to(d, DOWN, buff=0.25)
        c = M(r"\sigma\in\Sigma_{\mathbf{s},s}\ \longmapsto\ c(\sigma)\in\mathrm{T}_{\Lambda}(\mathord{\downarrow}\varphi^{\star}(\mathbf{s}))_{\varphi(s)}", 0.75).next_to(phi, DOWN, buff=0.25)
        self.play(Write(d), run_time=1.0)
        self.play(Write(phi), run_time=0.9)
        self.play(Write(c), run_time=1.6)

        self.cue(1)
        self.play(VGroup(d, phi, c).animate.scale(0.8).to_edge(UP, buff=0.9), run_time=0.6)
        ex = M(rf"\mathbf{{c}}\colon{SIG}\to{SIG},\quad\varphi=\mathrm{{id}}_S", 0.72).move_to(UP * 0.7 + LEFT * 3.0)
        r1 = M(r"c(\sigma)=\sigma(v^{s}_{0},\tau(v^{s}_{0}))", 0.75).next_to(ex, DOWN, buff=0.35, aligned_edge=LEFT)
        r2 = M(r"c(\tau)=\tau(v^{s}_{0})", 0.75).next_to(r1, DOWN, buff=0.25, aligned_edge=LEFT)
        self.play(Write(ex), run_time=1.0)
        self.play(Write(r1), run_time=1.2)
        # The term as a tree, with the sorts checked.
        root = op_box(r"\sigma", size=0.55).move_to(RIGHT * 3.0 + UP * 0.6)
        leaf1 = MathTex(r"v^{s}_{0}", color=S_).scale(0.7).move_to(RIGHT * 2.2 + DOWN * 0.5)
        tau = op_box(r"\tau", size=0.5).move_to(RIGHT * 3.8 + DOWN * 0.5)
        leaf2 = MathTex(r"v^{s}_{0}", color=S_).scale(0.7).move_to(RIGHT * 3.8 + DOWN * 1.5)
        e = VGroup(Line(root.get_bottom(), leaf1.get_top(), color=GREY_B), Line(root.get_bottom(), tau.get_top(), color=GREY_B),
                   Line(tau.get_bottom(), leaf2.get_top(), color=GREY_B))
        chips = VGroup(MathTex("s", color=S_).scale(0.6).next_to(root, RIGHT, buff=0.15),
                       MathTex("t", color=T_).scale(0.6).next_to(tau, RIGHT, buff=0.15))
        self.play(FadeIn(root), FadeIn(tau), FadeIn(leaf1), FadeIn(leaf2), Create(e), run_time=1.2)
        self.play(FadeIn(chips), Indicate(chips[1]), run_time=1.0)
        self.play(Write(r2), run_time=0.9)

        self.cue(2)
        self.play(FadeOut(VGroup(ex, r1, r2, root, tau, leaf1, leaf2, e, chips)), run_time=0.6)
        lv, note = two_levels(rf"\mathbf{{c}}\colon{SIG}\to{LAM}", r"\mathbf{c}^{\ast}\colon\mathsf{Alg}(\Lambda)\to\mathsf{Alg}(\Sigma)", width=5.5, center=DOWN * 0.1)
        self.play(GrowArrow(lv[0]), Write(lv[1]), run_time=1.0)
        self.play(GrowArrow(lv[2]), Write(lv[3]), run_time=1.0)

        self.cue(3)
        self.play(lv.animate.scale(0.75).move_to(LEFT * 3.3 + DOWN * 0.3), run_time=0.7)
        B = Ellipse(width=2.4, height=1.6, color=GREY_B).set_fill(GREY_B, 0.08).move_to(RIGHT * 1.5 + DOWN * 0.3)
        Bl = MathTex(r"\mathbf{B}").scale(0.7).next_to(B, UP, buff=0.05)
        Bphi = MathTex(r"B_{\varphi(s)}", color=GREY_A).scale(0.6).move_to(B)
        cB = Ellipse(width=2.4, height=1.6, color=S_).set_fill(S_, 0.12).move_to(RIGHT * 4.7 + DOWN * 0.3)
        cBl = MathTex(r"\mathbf{c}^{\ast}(\mathbf{B})", color=S_).scale(0.7).next_to(cB, UP, buff=0.05)
        cBs = MathTex(r"\text{sort } s", color=S_).scale(0.6).move_to(cB)
        arr = Arrow(B.get_right(), cB.get_left(), buff=0.1, color=FUNCTOR_COLOR, stroke_width=4)
        self.play(FadeIn(B), FadeIn(Bl), FadeIn(Bphi), run_time=0.8)
        self.play(GrowArrow(arr), FadeIn(cB), FadeIn(cBl), TransformFromCopy(Bphi, cBs), run_time=1.2)
        ev = M(r"\sigma^{\mathbf{c}^{\ast}(\mathbf{B})}=c(\sigma)^{\mathbf{B}}", 0.75).next_to(VGroup(B, cB), DOWN, buff=0.4)
        self.play(Write(ev), run_time=1.2)

        self.cue(4)
        self.play(Indicate(lv[0], color=DERIV_COLOR), run_time=0.8)
        self.play(Indicate(lv[2], color=FUNCTOR_COLOR), run_time=0.8)
        self.finish()


class Scene10Obstacles(V3Scene):
    scene_id = 10
    part = 2

    def construct(self):
        h = self.head(r"\dots but derivors are not enough")
        divider = DashedLine(UP * 2.6, DOWN * 3.1, color=GREY_D)
        self.play(Create(divider), run_time=0.5)

        self.cue(1)
        t1 = T(r"1. keep only part of the elements", 0.65).move_to(LEFT * 3.6 + UP * 2.3)
        As = sort_bag("s", r"\mathsf{A}_s", 3.4, 1.8, dims=(0, 0, 0, 1, 1, 1, 2, 2, 2)).move_to(LEFT * 3.6 + UP * 0.9)
        self.play(FadeIn(t1), FadeIn(As), run_time=1.0)
        keep = T(r"a derivor keeps the whole carrier", 0.6, GREY_A).move_to(LEFT * 3.6 + DOWN * 2.6)
        self.play(FadeIn(keep), run_time=0.6)

        self.cue(2)
        g = gate(rf"v^{{s}}_{{0}}{N.EEQ}{N.sc('1', 's')}(v^{{s}}_{{0}})", width=3.0)
        g[0].move_to(LEFT * 3.6 + DOWN * 0.3)
        g[1].scale(0.95).next_to(g[0], DOWN, buff=0.12)
        self.play(Create(g[0]), Write(g[1]), run_time=1.0)
        cells = As[2]
        passing = [c for c in cells if c.cell_dim <= 1]
        blocked = [c for c in cells if c.cell_dim > 1]
        dst = Rectangle(width=3.2, height=0.6, color=S_).set_fill(S_, 0.1).move_to(LEFT * 3.6 + DOWN * 1.8)
        dl = MathTex(r"A_{(1,s)}", color=S_).scale(0.55).next_to(dst, LEFT, buff=0.1)
        pos = [dst.get_left() + RIGHT * (0.35 + 0.42 * i) for i in range(len(passing))]
        self.play(FadeIn(dst), FadeIn(dl), run_time=0.4)
        self.play(LaggedStart(*[c.copy().animate.move_to(p) for c, p in zip(passing, pos)], lag_ratio=0.08),
                  *[c.animate.set_opacity(0.25) for c in blocked], run_time=1.6)

        self.cue(3)
        t2 = T(r"2. domains that no term expresses", 0.65).move_to(RIGHT * 3.6 + UP * 2.3)
        self.play(FadeIn(t2), run_time=0.6)

        self.cue(4)
        r = M(rf"{N.comp('k', 's')}\ \longmapsto\ v^{{s}}_{{0}}", 0.85).move_to(RIGHT * 3.6 + UP * 1.4)
        allp = T(r"defined at every pair", 0.6, GREY_A).next_to(r, DOWN, buff=0.2)
        self.play(Write(r), run_time=1.0)
        self.play(FadeIn(allp), run_time=0.6)

        self.cue(5)
        need = M(rf"v^{{s}}_{{0}}{N.comp('k', 's')}v^{{s}}_{{1}}\text{{ defined}}\iff v^{{s}}_{{0}}=v^{{s}}_{{1}}", 0.72).move_to(RIGHT * 3.6 + UP * 0.1)
        no = T(r"no term can say this", 0.65, RED).next_to(need, DOWN, buff=0.2)
        self.play(Write(need), run_time=1.4)
        self.play(FadeIn(no), run_time=0.6)

        self.cue(6)
        x = Dot(RIGHT * 2.6 + DOWN * 1.8)
        y = Dot(RIGHT * 4.6 + DOWN * 1.8)
        xl = MathTex("x").scale(0.7).next_to(x, DOWN, buff=0.1)
        yl = MathTex("y").scale(0.7).next_to(y, DOWN, buff=0.1)
        lx = CurvedArrow(x.get_center() + LEFT * 0.1 + UP * 0.1, x.get_center() + RIGHT * 0.1 + UP * 0.1, angle=-1.6 * PI, color=ID_COLOR, stroke_width=3, tip_length=0.12)
        ly = CurvedArrow(y.get_center() + LEFT * 0.1 + UP * 0.1, y.get_center() + RIGHT * 0.1 + UP * 0.1, angle=-1.6 * PI, color=ID_COLOR, stroke_width=3, tip_length=0.12)
        disc = T(r"a set as a discrete category", 0.6, GREY_A).move_to(RIGHT * 3.6 + DOWN * 2.6)
        self.play(FadeIn(VGroup(x, y, xl, yl)), Create(lx), Create(ly), FadeIn(disc), run_time=1.0)
        okx = M(r"(x,x)\ \checkmark", 0.65, GREEN).move_to(RIGHT * 2.6 + DOWN * 1.05)
        noxy = M(r"(x,y)\ \times", 0.65, RED).move_to(RIGHT * 4.6 + DOWN * 1.05)
        self.play(FadeIn(okx), run_time=0.6)
        self.play(FadeIn(noxy), run_time=0.6)
        self.finish()


class Scene11GeneralizedHepDerivors(V3Scene):
    scene_id = 11
    part = 2

    def construct(self):
        self.head(r"Generalized hep-derivors")

        self.cue(1)
        d = M(rf"{N.derivor()}\colon{SIG}\to{LAM}", 0.8, DERIV_COLOR).move_to(UP * 2.3)
        hs = T(r"between hep-signatures", 0.6, GREY_A).next_to(d, DOWN, buff=0.15)
        self.play(Write(d), FadeIn(hs), run_time=1.4)
        row1 = MathTex(r"s", r"\longmapsto", r"\varphi(s)", r"\;+\;", r"\mathrm{Dom}^{(\varphi,c)}_{s}").scale(0.8)
        row1[1].set_color(DERIV_COLOR)
        row1[4].set_color(DERIV_COLOR)
        dn = T(r"existence equations in one variable $v^{\varphi(s)}_{0}$", 0.6, DERIV_COLOR)
        row2 = MathTex(r"\sigma", r"\longmapsto", r"c(\sigma)").scale(0.8)
        row2[1].set_color(DERIV_COLOR)
        tn = T(r"a term", 0.6, GREY_A)
        grp = VGroup(row1, dn, row2, tn).arrange(DOWN, buff=0.22).next_to(hs, DOWN, buff=0.35)
        self.cue(1, 3.0)
        self.play(Write(row1[:3]), run_time=0.9)
        self.play(Write(row1[3:]), FadeIn(dn), run_time=1.2)
        self.cue(1, 9.5)
        self.play(Write(row2), FadeIn(tn), run_time=1.0)

        self.cue(2)
        self.play(FadeOut(VGroup(hs, grp)), d.animate.scale(0.8).to_edge(UP, buff=0.9), run_time=0.6)
        B = Ellipse(width=3.2, height=1.8, color=GREY_B).set_fill(GREY_B, 0.08).move_to(LEFT * 4.2 + UP * 0.9)
        Bl = MathTex(r"\mathbf{B}").scale(0.7).next_to(B, UP, buff=0.05)
        rng = np.random.default_rng(5)
        dots = VGroup(*[Dot(B.get_center() + np.array([(i % 4 - 1.5) * 0.6, (i // 4 - 1) * 0.45, 0]), radius=0.06, color=GREY_A) for i in range(12)])
        g = gate(r"\mathrm{Dom}^{(\varphi,c)}_{s}", width=2.8)
        g[0].move_to(LEFT * 4.2 + DOWN * 0.45)
        g[1].scale(0.9).next_to(g[0], RIGHT, buff=0.15)
        self.play(FadeIn(B), FadeIn(Bl), FadeIn(dots), Create(g), run_time=1.0)
        keep = [dots[i] for i in (0, 2, 5, 7, 9, 10)]
        drop = [dots[i] for i in (1, 3, 4, 6, 8, 11)]
        pos = [LEFT * 4.2 + DOWN * 1.6 + RIGHT * (i - 2.5) * 0.45 for i in range(6)]
        self.play(LaggedStart(*[k.animate.move_to(p).set_color(DERIV_COLOR) for k, p in zip(keep, pos)], lag_ratio=0.08),
                  *[x.animate.set_opacity(0.25) for x in drop], run_time=1.4)
        cl = M(r"B_{\mathrm{Dom}^{(\varphi,c)}}", 0.65, DERIV_COLOR).move_to(LEFT * 4.2 + DOWN * 2.2)
        tr = T(r"cells of " + "$" + N.induced(arg=r"\mathbf{B}") + "$", 0.6, DERIV_COLOR).next_to(cl, RIGHT, buff=0.2)
        self.play(FadeIn(cl), FadeIn(tr), run_time=0.7)

        self.cue(3)
        q = M(rf"\sigma^{{{N.induced(arg=BB)}}}\text{{ is defined at }}\mathbf{{b}}\iff", 0.72).move_to(RIGHT * 2.2 + UP * 1.3)
        self.play(Write(q), run_time=1.2)

        self.cue(4)
        checks = VGroup(
            VGroup(MathTex(r"\checkmark", color=YELLOW).scale(0.8), M(rf"{N.induced(arg=BB)}\models\mathrm{{def}}(\sigma)[\mathbf{{b}}]", 0.68)),
            VGroup(MathTex(r"\checkmark", color=GREEN).scale(0.8), M(r"c(\sigma)^{\mathbf{B}}\text{ is defined at }\mathbf{b}", 0.68)),
            VGroup(MathTex(r"\checkmark", color=DERIV_COLOR).scale(0.8), M(r"c(\sigma)^{\mathbf{B}}(\mathbf{b})\text{ is a cell}", 0.68)),
        )
        for c in checks:
            c.arrange(RIGHT, buff=0.2)
        checks.arrange(DOWN, aligned_edge=LEFT, buff=0.3).next_to(q, DOWN, buff=0.4)
        for c, t in zip(checks, [0.0, 2.6, 4.6]):
            self.cue(4, t)
            self.play(FadeIn(c, shift=RIGHT * 0.2), run_time=0.7)

        self.cue(5)
        s1 = T(r"obstacle 1 $\to$ the domains", 0.6, DERIV_COLOR).next_to(checks, DOWN, buff=0.4, aligned_edge=LEFT)
        s2 = T(r"obstacle 2 $\to$ the first condition", 0.6, YELLOW).next_to(s1, DOWN, buff=0.15, aligned_edge=LEFT)
        self.play(FadeIn(s1), Indicate(g[0], color=DERIV_COLOR), run_time=1.0)
        self.play(FadeIn(s2), Indicate(checks[0], color=YELLOW), run_time=1.0)

        self.cue(6)
        lv = VGroup(M(rf"{N.sc('k','s')},\ {N.tg('k','s')}", 0.6), M(N.comp("k", "s"), 0.75)).arrange(UP, buff=0.45)
        lv.to_corner(DR, buff=0.6).shift(UP * 0.4)
        up = Arrow(lv[0].get_top(), lv[1].get_bottom(), buff=0.05, color=GREY_B, stroke_width=3, max_tip_length_to_length_ratio=0.3)
        rec = T(r"by well-founded recursion", 0.6, GREY_A).next_to(lv, LEFT, buff=0.4)
        self.play(FadeOut(VGroup(s1, s2)), FadeIn(lv), GrowArrow(up), FadeIn(rec), run_time=0.8)
        self.play(Indicate(lv[0], color=DERIV_COLOR), run_time=0.6)
        self.play(Indicate(lv[1], color=DERIV_COLOR), run_time=0.6)
        self.finish()


class Scene12LaxComposition(V3Scene):
    scene_id = 12
    part = 2

    def construct(self):
        self.head(r"Weak algebras and lax composition")
        weak = M(rf"\mathrm{{Dom}}(\sigma^{{{N.induced(arg=BB)}}})\subseteq B_{{\mathrm{{def}}(\sigma)}}", 0.8).move_to(UP * 1.8)
        wl = T(r"always a \textbf{weak} $\mathbf{\Sigma}$-algebra", 0.65).next_to(weak, UP, buff=0.25)
        self.play(FadeIn(wl), Write(weak), run_time=1.4)

        self.cue(1)
        cmp = M(r"\text{ep-algebra: }\ \mathrm{Dom}(\sigma^{\mathbf{A}})=A_{\mathrm{def}(\sigma)}", 0.7, GREY_A).next_to(weak, DOWN, buff=0.35)
        self.play(FadeIn(cmp), run_time=0.8)

        self.cue(2)
        crit = T(r"an ep-algebra $\iff$ on the domain conditions,\\the terms are defined and give cells", 0.62, GREEN).next_to(cmp, DOWN, buff=0.35)
        self.play(FadeIn(crit, shift=UP * 0.1), run_time=0.9)

        self.cue(3)
        self.play(FadeOut(VGroup(weak, wl, cmp, crit)), run_time=0.6)
        divider = DashedLine(UP * 2.6, DOWN * 3.1, color=GREY_D).shift(LEFT * 2.0)
        box = RoundedRectangle(corner_radius=0.2, width=3.0, height=2.2, color=GREY_B).move_to(LEFT * 4.6 + UP * 0.6)
        Cl = MathTex(r"\mathbf{C}").scale(0.8).next_to(box, UP, buff=0.1)
        zero = obj("0", box.get_center() + LEFT * 0.7 + DOWN * 0.3, DOWN)
        one = obj("1", box.get_center() + RIGHT * 0.7 + DOWN * 0.3, DOWN)
        consts = M(r"z^{\mathbf{C}}=0,\ \ o^{\mathbf{C}}=1", 0.65).next_to(box, DOWN, buff=0.2)
        self.play(Create(divider), run_time=0.4)

        self.cue(4)
        self.play(FadeIn(box), FadeIn(Cl), FadeIn(zero), FadeIn(one), FadeIn(consts), run_time=1.0)
        chain = VGroup(
            M(r"\mathbf{\Sigma}:\ \text{sort } s", 0.65),
            M(r"\mathbf{\Lambda}:\ \text{sort } t,\ u\in\Lambda_{(t),t}", 0.65),
            M(r"\mathbf{\Omega}:\ \text{sort } w,\ z,o\in\Omega_{\lambda,w}", 0.65),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.75).move_to(RIGHT * 1.2 + UP * 0.9)
        cd = VGroup(*[Arrow(chain[i].get_bottom() + LEFT * 1.0, chain[i + 1].get_top() + LEFT * 1.0, buff=0.08, color=DERIV_COLOR, stroke_width=3,
                            max_tip_length_to_length_ratio=0.3) for i in range(2)])
        cdl = VGroup(MathTex(r"\mathbf{c}", color=DERIV_COLOR).scale(0.65).next_to(cd[0], LEFT, buff=0.08),
                     MathTex(r"\mathbf{d}", color=DERIV_COLOR).scale(0.65).next_to(cd[1], LEFT, buff=0.08))
        self.play(FadeIn(chain), GrowArrow(cd[0]), GrowArrow(cd[1]), FadeIn(cdl), run_time=1.2)

        self.cue(5)
        hl = SurroundingRectangle(VGroup(chain[1], chain[2]), color=YELLOW, buff=0.12)
        dd = M(r"\mathrm{Dom}^{\mathbf{d}}_{t}=\{v^{w}_{0}" + N.EEQ + r"z\},\quad d(u)=o", 0.62, DERIV_COLOR).move_to(RIGHT * 2.3 + DOWN * 1.65)
        sel = SurroundingRectangle(zero, color=DERIV_COLOR, buff=0.1, corner_radius=0.08)
        self.play(Create(hl), Write(dd), run_time=1.2)
        self.play(Create(sel), run_time=0.6)
        u = CurvedArrow(zero[0].get_center() + UP * 0.15, one[0].get_center() + UP * 0.15, angle=-PI / 2.5, color=OP_COLOR, stroke_width=3, tip_length=0.15)
        ul = MathTex("u", color=OP_COLOR).scale(0.65).next_to(u, UP, buff=0.03)
        self.play(Create(u), FadeIn(ul), run_time=0.8)

        self.cue(6)
        cross = Cross(u, stroke_color=RED, stroke_width=5).scale(0.5)
        why = T(r"$u$ nowhere defined in $\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{C})$", 0.6, RED).next_to(consts, DOWN, buff=0.2)
        self.play(Create(cross), FadeIn(why), run_time=1.0)

        self.cue(7)
        hl2 = SurroundingRectangle(VGroup(chain[0], chain[1]), color=YELLOW, buff=0.12)
        dc = M(r"\mathrm{Dom}^{\mathbf{c}}_{s}=\{u(v^{t}_{0})" + N.EEQ + r"u(v^{t}_{0})\}", 0.62, DERIV_COLOR).move_to(dd)
        self.play(ReplacementTransform(hl, hl2), ReplacementTransform(dd, dc), run_time=1.0)
        r1 = M(r"\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{C}))=\varnothing", 0.68).next_to(dc, DOWN, buff=0.25)
        self.play(Write(r1), run_time=1.0)
        hl3 = SurroundingRectangle(chain, color=YELLOW, buff=0.12)
        r2 = M(r"(\mathbf{d}\circ\mathbf{c})^{\ast}_{\mathfrak{gd}}(\mathbf{C})=\{0\}", 0.68).next_to(r1, DOWN, buff=0.2)
        self.cue(7, 4.2)
        self.play(ReplacementTransform(hl2, hl3), Write(r2), Indicate(sel, color=DERIV_COLOR), run_time=1.2)

        self.cue(8)
        self.play(FadeOut(VGroup(dc, r1, r2, hl3, why)), run_time=0.5)
        kap = M(r"\kappa^{\mathbf{c},\mathbf{d}}_{\mathbf{C}}\colon\mathbf{c}^{\ast}_{\mathfrak{gd}}(\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{C}))\hookrightarrow(\mathbf{d}\circ\mathbf{c})^{\ast}_{\mathfrak{gd}}(\mathbf{C})", 0.6).move_to(RIGHT * 2.3 + DOWN * 1.7)
        here = M(r"\varnothing\subsetneq\{0\}", 0.7, YELLOW).next_to(kap, DOWN, buff=0.15)
        lax = T(r"a normal \textbf{lax} indexed category", 0.65, YELLOW).next_to(here, DOWN, buff=0.15)
        self.play(Write(kap), run_time=1.4)
        self.play(FadeIn(here), FadeIn(lax), run_time=0.8)
        rec = recap_card([r"sorts $\mapsto$ sorts with domains", r"symbols $\mapsto$ terms",
                          r"transformed algebra by recursion", r"lax under composition"], "Part III").to_corner(DL, buff=0.4).shift(UP * 0.35)
        self.play(FadeIn(rec), run_time=0.7)
        self.finish()


# ---------------------------------------------------------------------------------------------
# Part IV — Dimensions
# ---------------------------------------------------------------------------------------------

def bags_and_grid(bag_x=-4.6, grid_x=3.4, y=-0.6, rows=3):
    As = sort_bag("s", r"\mathsf{A}_s", 1.9, 1.3, dims=(0, 1, 2)).move_to(np.array([bag_x, y + 0.9, 0]))
    At = sort_bag("t", r"\mathsf{A}_t", 1.9, 1.3, dims=(0, 1)).move_to(np.array([bag_x, y - 1.0, 0]))
    cols = drawer_grid(rows=rows, width=1.9, height=0.6, top="n").move_to(np.array([grid_x, y, 0]))
    return As, At, cols


class Scene13Graduation(V3Scene):
    scene_id = 13
    part = 3

    def construct(self):
        self.head(r"Graduation")
        lv, note = two_levels(rf"{N.functor('Gd', 'n', bold=True)}\colon{N.ext(htg=True)}\to{N.ext()}",
                              rf"{N.functor('Gd', 'n')}\colon{N.cat()}\to{N.cat(htg=True)}", width=5.5, center=UP * 1.0, left_to_right=True)
        self.play(GrowArrow(lv[0]), Write(lv[1]), run_time=1.2)
        self.play(GrowArrow(lv[2]), Write(lv[3]), run_time=1.2)

        self.cue(1)
        note.next_to(lv, DOWN, buff=0.3)
        self.play(FadeIn(note), Indicate(lv[2], color=FUNCTOR_COLOR), run_time=1.0)
        self.cue(2)
        trans = T(r"heterogeneous symbols $\mapsto$ homogeneous terms\qquad homogeneous algebras $\mapsto$ heterogeneous ones", 0.6, GREY_A).next_to(note, DOWN, buff=0.2)
        self.play(FadeIn(trans), run_time=0.9)

        self.cue(3)
        self.play(FadeOut(VGroup(note, trans)), lv.animate.scale(0.6).to_edge(UP, buff=0.85), run_time=0.7)
        rules = VGroup(
            M(r"(k,s)\longmapsto s", 0.65),
            M(rf"\mathrm{{Dom}}_{{(k,s)}}=\{{v^{{s}}_{{0}}{N.EEQ}{N.sc('k','s')}(v^{{s}}_{{0}})\}}\ (k\in n)", 0.62, DERIV_COLOR),
            M(r"\mathrm{Dom}_{(n,s)}=\varnothing", 0.62, DERIV_COLOR),
            M(r"\sigma_k\longmapsto\sigma(v^{s}_{0},v^{t}_{1})", 0.65),
            M(rf"{N.gsc('j','k','s')}\longmapsto{N.sc('j','s')}(v^{{s}}_{{0}})", 0.65),
            M(rf"{N.gid('k','j','s')}\longmapsto v^{{s}}_{{0}}", 0.65),
            M(rf"{N.gcomp('j','k','s')}\longmapsto v^{{s}}_{{0}}{N.comp('j','s')}v^{{s}}_{{1}}", 0.65),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.17).to_edge(LEFT, buff=0.5).shift(DOWN * 0.35)
        self.play(Write(rules[0]), run_time=0.8)
        self.cue(4)
        self.play(Write(rules[1]), Write(rules[2]), run_time=1.4)

        self.cue(5)
        As, At, cols = bags_and_grid(bag_x=1.0, grid_x=4.8, y=-0.75)
        self.play(FadeIn(As), FadeIn(At), FadeIn(cols), run_time=0.8)
        moves = []
        for bagg, ci in [(As, 0), (At, 1)]:
            for k in range(3):
                members = [c for c in bagg[2] if c.cell_dim <= k]
                for c, p in zip(members, slots(cols[ci][k], max(len(members), 1), left=0.95)):
                    moves.append(c.copy().animate.move_to(p).scale(0.7))
        self.play(LaggedStart(*moves, lag_ratio=0.03), run_time=3.0)
        many = T(r"a 0-cell lands in every row", 0.6, GREY_A).next_to(cols, DOWN, buff=0.15)
        self.play(FadeIn(many), run_time=0.6)

        self.cue(6)
        for r in rules[3:]:
            self.play(Write(r), run_time=0.9)
        why = T(r"a lower cell is already its own identity", 0.6, ID_COLOR).next_to(rules, DOWN, buff=0.2, aligned_edge=LEFT)
        self.play(FadeIn(why), Indicate(rules[5], color=ID_COLOR), run_time=1.0)
        self.finish()


class Scene14Unification(V3Scene):
    scene_id = 14
    part = 3

    def construct(self):
        self.head(r"Unification, and the equivalence")
        lv, _ = two_levels(rf"{N.functor('Uf', 'n', bold=True)}\colon{N.ext()}\to{N.ext(htg=True)}",
                           rf"{N.functor('Uf', 'n')}\colon{N.cat(htg=True)}\to{N.cat()}", width=5.5, center=UP * 1.5)
        lv.scale(0.75).to_edge(UP, buff=0.85)
        self.play(FadeIn(lv), run_time=1.0)

        self.cue(1)
        rules = VGroup(
            M(r"s\longmapsto(n,s)", 0.65),
            M(r"\sigma\longmapsto\sigma_n(v^{(n,s)}_{0},v^{(n,t)}_{1})", 0.65),
            M(rf"{N.comp('k','s')}\longmapsto v^{{(n,s)}}_{{0}}{N.gcomp('k','n','s')}v^{{(n,s)}}_{{1}}", 0.65),
            M(rf"{N.sc('k','s')}\longmapsto{N.gid('n','k','s')}({N.gsc('k','n','s')}(v^{{(n,s)}}_{{0}}))", 0.65),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.22).to_edge(LEFT, buff=0.5).shift(DOWN * 0.1)
        cols = drawer_grid(rows=3, width=1.9, height=0.6, top="n").move_to(RIGHT * 2.3 + DOWN * 0.4)
        for ci, n_cells in [(0, (3, 4, 3)), (1, (2, 3, 2))]:
            for k in range(3):
                for p in slots(cols[ci][k], n_cells[k], left=0.65):
                    cols[ci][k].add(cell_glyph(k, scale=0.7).move_to(p))
        As = sort_bag("s", r"\mathsf{A}_s", 1.8, 1.2, dims=()).move_to(RIGHT * 5.7 + UP * 0.4)
        At = sort_bag("t", r"\mathsf{A}_t", 1.8, 1.2, dims=()).move_to(RIGHT * 5.7 + DOWN * 1.3)
        self.play(FadeIn(cols), Write(rules[0]), run_time=1.2)
        self.play(Write(rules[1]), run_time=1.0)
        self.play(Write(rules[2]), run_time=1.2)
        self.play(Write(rules[3]), run_time=1.4)
        tops = VGroup(*[c.copy() for ci in range(2) for c in cols[ci][2][2:]])
        targets = [As[0].get_center() + RIGHT * (i - 1) * 0.45 for i in range(3)] + [At[0].get_center() + RIGHT * (i - 0.5) * 0.45 for i in range(2)]
        self.play(FadeIn(As), FadeIn(At), *[t.animate.move_to(p) for t, p in zip(tops, targets)], run_time=1.6)
        path = VGroup(Arrow(cols[0][2][0].get_left() + DOWN * 0.1, cols[0][0][0].get_left() + UP * 0.1, buff=0.05, color=STRUCT_COLOR, stroke_width=3,
                            max_tip_length_to_length_ratio=0.12),
                      DashedLine(cols[0][0][0].get_left() + LEFT * 0.15 + UP * 0.1, cols[0][2][0].get_left() + LEFT * 0.15 + DOWN * 0.1,
                                 color=ID_COLOR).add_tip(tip_length=0.12))
        self.play(Create(path), Indicate(rules[3]), run_time=1.4)

        self.cue(2)
        self.play(FadeOut(VGroup(rules, path, cols, As, At, tops)), run_time=0.6)
        f1 = M(rf"{N.functor('Uf','n')}\circ{N.functor('Gd','n')}=\mathrm{{Id}}", 0.9).move_to(LEFT * 3.0 + UP * 0.6)
        self.play(Write(f1), run_time=1.0)
        self.play(Circumscribe(f1, color=GREEN), run_time=1.0)

        self.cue(3)
        f2 = M(rf"\theta\colon\mathrm{{Id}}\cong{N.functor('Gd','n')}\circ{N.functor('Uf','n')}", 0.9).move_to(RIGHT * 3.0 + UP * 0.6)
        self.play(Write(f2), run_time=1.2)
        self.cue(4)
        th = M(rf"\theta(u)={N.gid('n','k','s')}(u),\quad u\in A_{{(k,s)}}", 0.75, ID_COLOR).next_to(f2, DOWN, buff=0.35)
        self.play(Write(th), Circumscribe(f2, color=YELLOW), run_time=1.4)

        self.cue(5)
        adj = M(rf"{N.functor('Gd','n')}\dashv{N.functor('Uf','n')}", 1.0, FUNCTOR_COLOR).move_to(DOWN * 1.4)
        unit = T(r"unit $\mathrm{id}$, counit $\theta^{-1}$: an adjoint equivalence", 0.65, FUNCTOR_COLOR).next_to(adj, DOWN, buff=0.25)
        self.play(Write(adj), run_time=1.0)
        self.play(FadeIn(unit), run_time=0.8)

        self.cue(6)
        eq = M(rf"{N.cat()}\simeq{N.cat(htg=True)}", 0.85).next_to(unit, DOWN, buff=0.35)
        self.play(Write(eq), run_time=1.2)
        self.finish()


class Scene15DiscretizationTruncation(V3Scene):
    scene_id = 15
    part = 3

    def construct(self):
        self.head(r"Discretization and truncation")
        floors = tower([N.cat("0"), N.cat("1"), N.cat("2")], spacing=1.25, width=2.6)
        dots = MathTex(r"\vdots").next_to(floors, UP, buff=0.12)
        twr = VGroup(floors, dots).move_to(LEFT * 4.5 + DOWN * 0.4)
        self.play(LaggedStartMap(FadeIn, floors, shift=UP * 0.2, lag_ratio=0.2), FadeIn(dots), run_time=1.0)
        t_arrow = CurvedArrow(floors[2].get_left() + LEFT * 0.05, floors[1].get_left() + LEFT * 0.05, angle=TAU / 4,
                              color=FUNCTOR_COLOR, stroke_width=4, tip_length=0.2)
        t_lab = M(N.functor("Tr", "1", "2"), 0.6, FUNCTOR_COLOR).next_to(t_arrow, LEFT, buff=0.05)
        self.play(Create(t_arrow), Write(t_lab), run_time=0.8)
        tr = VGroup(M(rf"{N.functor('Tr','m','n',bold=True)}\colon{N.ext('m')}\hookrightarrow{N.ext('n')}", 0.7, DERIV_COLOR),
                    M(rf"\mathrm{{Dom}}_{{s}}=\{{v^{{s}}_{{0}}{N.EEQ}{N.sc('m','s')}(v^{{s}}_{{0}})\}}", 0.68, DERIV_COLOR),
                    M(rf"{N.functor('Tr','m','n')}\colon{N.cat('n')}\to{N.cat('m')}", 0.68, FUNCTOR_COLOR)).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        tr.move_to(RIGHT * 1.2 + UP * 1.6)
        self.play(Write(tr[0]), run_time=1.2)
        self.play(Write(tr[2]), run_time=1.0)

        self.cue(1)
        self.play(Write(tr[1]), run_time=1.0)
        g = globe(RIGHT * 0.2 + DOWN * 1.0, RIGHT * 2.6 + DOWN * 1.0, f="f", g="g")
        self.play(FadeIn(g), run_time=0.6)
        self.play(g[4].animate.set_opacity(0.2), run_time=0.8)
        k1 = T(r"keeps only the $m$-cells", 0.6).next_to(g, RIGHT, buff=0.4)
        self.play(FadeIn(k1), run_time=0.5)

        self.cue(2)
        self.play(FadeOut(VGroup(tr, g, k1)), run_time=0.6)
        d_arrow = CurvedArrow(floors[1].get_right() + RIGHT * 0.05, floors[2].get_right() + RIGHT * 0.05, angle=TAU / 4,
                              color=FUNCTOR_COLOR, stroke_width=4, tip_length=0.2)
        d_lab = M(N.functor("Ds", "2", "1"), 0.6, FUNCTOR_COLOR).next_to(d_arrow, RIGHT, buff=0.05)
        self.play(Create(d_arrow), Write(d_lab), run_time=0.8)

        self.cue(3)
        ds = VGroup(M(rf"{N.functor('Ds','n','m',bold=True)}\colon{N.ext('n')}\to{N.ext('m')}", 0.7, DERIV_COLOR),
                    M(rf"{N.sc('k','s')},\ {N.tg('k','s')},\ {N.comp('k','s')}\ \longmapsto\ v^{{s}}_{{0}}\qquad(m\le k<n)", 0.68, DERIV_COLOR)).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        ds.move_to(RIGHT * 1.2 + UP * 1.7)
        self.play(Write(ds), run_time=1.6)
        X = Dot(RIGHT * 0.2 + DOWN * 0.3)
        Y = Dot(RIGHT * 2.6 + DOWN * 0.3)
        f = mor(X.get_center(), Y.get_center(), "f", angle=-TAU / 7)
        f2 = mor(X.get_center(), Y.get_center(), "f", angle=TAU / 7, label_dir=DOWN)
        self.play(FadeIn(X), FadeIn(Y), Create(f), run_time=0.7)
        self.play(TransformFromCopy(f, f2), run_time=0.6)
        idf = two_cell(f, f2, r"\mathrm{id}_f", color=ID_COLOR)
        self.play(FadeIn(idf), run_time=0.5)
        diag = M(rf"v^{{s}}_{{0}}{N.comp('k','s')}v^{{s}}_{{1}}\text{{ defined}}\iff v^{{s}}_{{0}}=v^{{s}}_{{1}}", 0.68).move_to(RIGHT * 1.5 + DOWN * 1.6)
        alone = T(r"imposed by the domain conditions alone", 0.6, YELLOW).next_to(diag, DOWN, buff=0.15)
        self.play(Write(diag), run_time=1.2)
        self.play(FadeIn(alone), run_time=0.6)

        self.cue(4)
        self.play(FadeOut(VGroup(ds, X, Y, f, f2, idf, diag, alone)), run_time=0.6)
        notinv = T(r"not inverse: truncation forgets the higher cells", 0.65).move_to(RIGHT * 1.3 + UP * 1.8)
        self.play(FadeIn(notinv), run_time=0.8)

        self.cue(6)
        bij = M(rf"{N.cat('n')}({N.functor('Ds','n','m')}(\calg{{A}}),\calg{{B}})\ \cong\ {N.cat('m')}(\calg{{A}},{N.functor('Tr','m','n')}(\calg{{B}}))", 0.62).move_to(RIGHT * 1.3 + UP * 0.6)
        self.play(Write(bij), run_time=1.8)
        a1 = Arrow(LEFT * 0.4 + DOWN * 0.5, RIGHT * 1.6 + DOWN * 0.5, buff=0, color=WHITE, stroke_width=3)
        a1l = M(rf"{N.functor('Ds','n','m')}(\calg{{A}})\to\calg{{B}}", 0.6).next_to(a1, DOWN, buff=0.1)
        a2 = Arrow(RIGHT * 2.4 + DOWN * 0.5, RIGHT * 4.4 + DOWN * 0.5, buff=0, color=WHITE, stroke_width=3)
        a2l = M(rf"\calg{{A}}\to{N.functor('Tr','m','n')}(\calg{{B}})", 0.6).next_to(a2, DOWN, buff=0.1)
        self.play(GrowArrow(a1), FadeIn(a1l), run_time=0.7)
        self.play(TransformFromCopy(a1, a2), FadeIn(a2l), run_time=0.9)

        self.cue(7)
        res = VGroup(M(rf"{N.functor('Tr','m','n')}\circ{N.functor('Ds','n','m')}=\mathrm{{Id}}", 0.75),
                     M(rf"{N.functor('Ds','n','m')}\dashv{N.functor('Tr','m','n')}", 0.8, FUNCTOR_COLOR),
                     T(r"unit $\mathrm{id}$, counit: the inclusion of the $m$-cells", 0.6)).arrange(DOWN, buff=0.18).move_to(RIGHT * 1.3 + DOWN * 2.0)
        self.play(Write(res[1]), FadeIn(res[2]), run_time=1.2)
        self.play(Write(res[0]), run_time=1.0)

        self.cue(8)
        gl = M(rf"{N.functor('Ds','n','m',htg=True)}\dashv{N.functor('Tr','m','n',htg=True)}", 0.65, GREY_A).next_to(notinv, DOWN, buff=0.2)
        self.play(FadeIn(gl), run_time=0.8)
        self.finish()


class Scene16AlgebraicSquare(V3Scene):
    scene_id = 16
    part = 3

    def construct(self):
        self.head(r"The algebraic square")
        gen = cat_square(r"\mathsf{C}", r"\mathsf{D}", r"\mathsf{C}'", r"\mathsf{D}'", w=2.0, h=1.3, scale=0.85, center=LEFT * 3.3 + UP * 0.3)
        gt, gb, gl_, gr = square_arrows(gen, gd="F", uf="G", ds="J", tr="K", scale=0.65)
        gb[2].become(MathTex("F'", color=FUNCTOR_COLOR).scale(0.65).move_to(gb[2]))
        gb[3].become(MathTex("G'", color=FUNCTOR_COLOR).scale(0.65).move_to(gb[3]))
        gr[2].become(MathTex("H", color=FUNCTOR_COLOR).scale(0.65).move_to(gr[2]))
        gr[3].become(MathTex("I", color=FUNCTOR_COLOR).scale(0.65).move_to(gr[3]))
        self.play(FadeIn(gen), run_time=0.6)

        self.cue(1)
        self.play(LaggedStartMap(Create, VGroup(gt, gb, gl_, gr), lag_ratio=0.2), run_time=1.6)
        al = M(r"\alpha\colon F'\circ J\cong H\circ F", 0.75).move_to(RIGHT * 2.6 + UP * 1.3)
        lab = VGroup(T(r"left adjoints commute", 0.6, GREY_A).next_to(al, DOWN, buff=0.12))
        be = M(r"\beta\colon G\circ I\cong K\circ G'", 0.75).next_to(lab[0], DOWN, buff=0.4)
        lab.add(T(r"right adjoints commute", 0.6, GREY_A).next_to(be, DOWN, buff=0.12))
        self.play(Write(al), FadeIn(lab[0]), run_time=1.4)
        self.play(Write(be), FadeIn(lab[1]), run_time=1.4)

        self.cue(2)
        self.play(FadeOut(VGroup(gen, gt, gb, gl_, gr, al, be, lab)), run_time=0.6)
        labels = square_labels(center=UP * 0.6, w=3.4, h=1.5)
        top, bot, left, right = functor_square(labels)
        fix_square(top, bot, left, right)
        self.play(FadeIn(labels), LaggedStartMap(Create, VGroup(top, bot, left, right), lag_ratio=0.15), run_time=1.4)
        p1 = VGroup(left[0], bot[0]).copy().set_color(YELLOW)
        p2 = VGroup(top[0], right[0]).copy().set_color(YELLOW)
        self.play(ShowPassingFlash(p1, time_width=0.7), ShowPassingFlash(p2, time_width=0.7), run_time=1.3)
        e1 = M(rf"{N.functor('Gd','n')}\circ{N.functor('Ds','n','m')}={N.functor('Ds','n','m',htg=True)}\circ{N.functor('Gd','m')}", 0.72).move_to(DOWN * 1.9)
        self.play(Write(e1), run_time=1.4)

        self.cue(3)
        p3 = VGroup(right[1], top[1]).copy().set_color(GREEN)
        p4 = VGroup(bot[1], left[1]).copy().set_color(GREEN)
        self.play(ShowPassingFlash(p3, time_width=0.7), ShowPassingFlash(p4, time_width=0.7), run_time=1.3)
        e2 = M(rf"\beta^{{(m,n)}}\colon{N.functor('Uf','m')}\circ{N.functor('Tr','m','n',htg=True)}\cong{N.functor('Tr','m','n')}\circ{N.functor('Uf','n')}", 0.72).next_to(e1, DOWN, buff=0.25)
        self.play(Write(e2), run_time=1.4)
        cap = T(r"an \textbf{algebraic square}: $\alpha=\mathrm{id}$, $\beta=\beta^{(m,n)}$", 0.62, FUNCTOR_COLOR).next_to(e2, DOWN, buff=0.25)
        self.play(FadeIn(cap), run_time=0.7)
        self.finish()


class Scene17DimensionOmega(V3Scene):
    scene_id = 17
    part = 3

    def construct(self):
        self.head(r"Dimension $\omega$")
        floors = tower([N.cat("0"), N.cat("1"), N.cat("2")], spacing=1.0, width=2.6)
        dots = MathTex(r"\vdots").next_to(floors, UP, buff=0.1)
        omega = VGroup(RoundedRectangle(corner_radius=0.12, width=2.6, height=0.65, color=FUNCTOR_COLOR),
                       MathTex(N.cat("omega")).scale(0.7)).next_to(dots, UP, buff=0.2)
        VGroup(floors, dots, omega).move_to(LEFT * 5.0 + DOWN * 0.3)
        self.play(LaggedStartMap(FadeIn, floors, shift=UP * 0.2, lag_ratio=0.2), FadeIn(dots), run_time=0.9)
        self.play(FadeIn(omega, shift=UP * 0.3), run_time=0.6)
        projs = VGroup(*[CurvedArrow(omega.get_right() + DOWN * 0.1, fl.get_right(), angle=-TAU / (5 + 2 * i),
                                     color=FUNCTOR_COLOR, stroke_width=3, tip_length=0.15) for i, fl in enumerate(floors)])
        pl = M(N.functor("Tr", "n", "omega"), 0.6, FUNCTOR_COLOR).next_to(projs[0], RIGHT, buff=0.05)
        self.play(LaggedStartMap(Create, projs, lag_ratio=0.25), Write(pl), run_time=1.4)
        lim = VGroup(M(rf"{N.cat('omega')}\cong\varprojlim_{{n}}{N.cat()}", 0.75),
                     M(rf"{N.cat('omega', htg=True)}\cong\varprojlim_{{n}}{N.cat(htg=True)}", 0.7, DRAWER_COLOR)).arrange(DOWN, buff=0.25)
        lim.move_to(RIGHT * 2.2 + UP * 1.9)
        self.play(Write(lim[0]), run_time=1.4)
        self.play(Write(lim[1]), run_time=1.4)

        self.cue(1)
        L = MathTex(r"\mathsf{L}").scale(0.9).move_to(LEFT * 1.0 + UP * 1.2)
        uniq = DashedLine(L.get_left(), omega.get_right() + RIGHT * 0.05, color=WHITE).add_tip(tip_length=0.15)
        ul = M(r"\exists!\,\langle F_k\rangle_{k\in\omega}", 0.6).next_to(uniq, UP, buff=0.02)
        fs = VGroup(*[Arrow(L.get_bottom(), fl.get_right() + RIGHT * 1.4, buff=0.1, color=GREY_B, stroke_width=2,
                            max_tip_length_to_length_ratio=0.08) for fl in floors[1:]])
        fl = M(r"F_n", 0.6, GREY_B).next_to(fs[1], RIGHT, buff=0.05)
        self.play(Write(L), Create(fs), Write(fl), run_time=1.0)
        self.play(Create(uniq), Write(ul), run_time=0.9)
        comp = T(r"$F_m=\mathrm{Tr}^{(m,n)}\circ F_n$: a compatible family", 0.6, GREY_A).move_to(RIGHT * 2.2 + UP * 0.4)
        self.play(FadeIn(comp), run_time=0.6)

        self.cue(2)
        n1 = T(r"$" + N.functor("Tr", "n", "omega") + r"$, $" + N.functor("Ds", "omega", "m") + r"$: induced by generalized hep-derivors", 0.6, DERIV_COLOR)
        n2 = T(r"$" + N.functor("Gd", "omega") + r"$: from the universal property", 0.6, FUNCTOR_COLOR)
        VGroup(n1, n2).arrange(DOWN, aligned_edge=LEFT, buff=0.2).move_to(RIGHT * 2.2 + DOWN * 0.5)
        self.play(FadeIn(n1, shift=UP * 0.1), run_time=0.8)
        self.cue(2, 6.0)
        self.play(FadeIn(n2, shift=UP * 0.1), run_time=0.8)

        self.cue(3)
        self.play(FadeOut(VGroup(floors, dots, omega, projs, pl, L, uniq, ul, fs, fl, comp, n1, n2)), lim.animate.scale(0.8).to_edge(UP, buff=0.85), run_time=0.8)
        ifs = T(r"if $S\neq\varnothing$", 0.7, YELLOW).move_to(UP * 1.3)
        self.play(FadeIn(ifs), run_time=0.6)

        self.cue(4)
        cols = VGroup()
        for k, (dim, name) in enumerate([(1, "g_0"), (2, "g_1"), (3, "g_2")]):
            g = cell_glyph(dim, scale=1.3)
            lab = MathTex(name).scale(0.7)
            d = T(f"a {k + 1}-cell", 0.6, GREY_A)
            cols.add(VGroup(g, lab, d).arrange(DOWN, buff=0.12))
        cols.add(MathTex(r"\cdots").scale(0.9))
        cols.arrange(RIGHT, buff=0.9).move_to(UP * 0.2)
        self.play(LaggedStartMap(FadeIn, cols, lag_ratio=0.2), run_time=1.2)
        prod = M(r"g=(g_k)_{k\in\omega}\ \text{ has no finite dimension}", 0.75, RED).next_to(cols, DOWN, buff=0.35)
        self.play(Write(prod), run_time=1.4)
        s1 = T(r"homogeneous: $" + N.cat("omega") + r"$ is \textbf{not} defined by QE-equations", 0.62).next_to(prod, DOWN, buff=0.35)
        self.play(FadeIn(s1), run_time=0.8)

        self.cue(5)
        s2 = T(r"heterogeneous: $" + N.cat("omega", htg=True) + r"=\mathsf{EPAlg}(\boldsymbol{\mathcal{C}}^{" + N.ext("omega", htg=True) + r"})$", 0.62, DRAWER_COLOR).next_to(s1, DOWN, buff=0.2)
        self.play(FadeIn(s2), run_time=0.8)
        self.finish()


class Scene18UnificationOmega(V3Scene):
    scene_id = 18
    part = 3

    def construct(self):
        self.head(r"Unification in dimension $\omega$")
        cols = drawer_grid(rows=4, width=1.8, height=0.5, gap=0.15).move_to(LEFT * 3.6 + DOWN * 0.2)
        for ci, counts in [(0, (2, 3, 2, 2)), (1, (1, 2, 2, 1))]:
            for k in range(4):
                for p in slots(cols[ci][k], counts[k], left=0.7):
                    cols[ci][k].add(cell_glyph(min(k, 3), scale=0.7).move_to(p))
        more = MathTex(r"\vdots", color=GREY_B).next_to(cols, UP, buff=0.05)
        self.play(FadeIn(cols), FadeIn(more), run_time=1.0)

        self.cue(1)
        ifs = T(r"if $S\neq\varnothing$", 0.65, YELLOW).move_to(RIGHT * 2.6 + UP * 2.0)
        self.play(FadeIn(ifs), run_time=0.6)
        self.cue(2)
        pick = SurroundingRectangle(cols[0][1], color=DERIV_COLOR, buff=0.05)
        pl = T(r"a generalized hep-derivor takes the cells of $s$ from one carrier $A_{\varphi(s)}$", 0.6, DERIV_COLOR).move_to(RIGHT * 2.6 + UP * 1.2)
        self.play(Create(pick), FadeIn(pl), run_time=1.0)
        self.play(*[Indicate(cols[0][k], color=FUNCTOR_COLOR) for k in range(4)], run_time=1.0)
        cross = Cross(pick, stroke_color=RED, stroke_width=5).scale(0.6)
        self.play(Create(cross), run_time=0.6)

        self.cue(3)
        self.play(FadeOut(VGroup(pick, cross, pl)), run_time=0.5)
        Bs = sort_bag("s", r"[B]_s", 2.6, 1.6, dims=()).move_to(RIGHT * 1.6 + DOWN * 0.1)
        Bt = sort_bag("t", r"[B]_t", 2.6, 1.6, dims=()).move_to(RIGHT * 4.8 + DOWN * 0.1)
        q = M(r"[B]_s=\coprod_{k\in\omega}B_{(k,s)}/\Theta_s", 0.75).move_to(RIGHT * 3.2 + UP * 1.3)
        self.play(FadeIn(Bs), FadeIn(Bt), Write(q), run_time=1.2)
        copies, targets = VGroup(), []
        for ci, bagg in [(0, Bs), (1, Bt)]:
            cells = [c for k in range(4) for c in cols[ci][k][2:]]
            for i, c in enumerate(cells):
                copies.add(c.copy())
                targets.append(bagg[0].get_center() + np.array([(i % 4 - 1.5) * 0.5, (1 - i // 4) * 0.42, 0]))
        self.play(LaggedStart(*[c.animate.move_to(p) for c, p in zip(copies, targets)], lag_ratio=0.03), run_time=1.6)
        glue = M(rf"x\ \sim\ {N.gid('k','j','s')}(x)\quad\leadsto\quad[x]_j", 0.7, ID_COLOR).next_to(VGroup(Bs, Bt), DOWN, buff=0.3)
        self.play(Write(glue), run_time=1.2)

        self.cue(4)
        self.play(FadeOut(VGroup(cols, more, copies, Bs, Bt, q, glue, ifs)), run_time=0.6)
        adj = M(rf"{N.functor('Gd','omega')}\dashv{N.functor('Uf','omega')}", 0.95, FUNCTOR_COLOR).move_to(UP * 1.6)
        an = T(r"an adjoint equivalence", 0.65, FUNCTOR_COLOR).next_to(adj, DOWN, buff=0.15)
        self.play(Write(adj), FadeIn(an), run_time=1.2)
        labels = square_labels(n="omega", center=DOWN * 0.9, w=2.9, h=1.0, scale=0.6)
        top, bot, left, right = functor_square(labels, n="omega", scale=0.5)
        fix_square(top, bot, left, right, n="omega", scale=0.5)
        self.play(FadeIn(labels), LaggedStartMap(Create, VGroup(top, bot, left, right), lag_ratio=0.15), run_time=1.6)
        rec = recap_card([r"presentation: an equivalence", r"dimension: an adjunction",
                          r"together: algebraic squares", r"$\omega$: limits and one quotient"], "Part IV").to_corner(UL, buff=0.4).shift(DOWN * 0.7)
        self.play(FadeIn(rec), run_time=0.7)
        self.finish()


# ---------------------------------------------------------------------------------------------
# Part V — Signatures
# ---------------------------------------------------------------------------------------------

class Scene19ChangeOfSignature(V3Scene):
    scene_id = 19
    part = 4

    def construct(self):
        self.head(r"Change of signature")
        d = M(rf"\mathbf{{c}}=(\varphi,c)\colon{SIG}\to{LAM}\ \text{{ in }}\mathsf{{Sig}}_{{\mathfrak{{d}}}}", 0.8, DERIV_COLOR).move_to(UP * 2.3)
        self.play(Write(d), run_time=1.2)

        self.cue(1)
        cs = VGroup(MathTex("s", color=S_), MathTex("t", color=T_)).arrange(DOWN, buff=0.5).scale(0.9).move_to(LEFT * 4.6 + UP * 0.9)
        cu = MathTex("u", color=SORT_COLORS["u"]).scale(0.9).move_to(LEFT * 2.2 + UP * 0.9)
        arrs = VGroup(*[Arrow(c.get_right(), cu.get_left(), buff=0.15, color=DERIV_COLOR, stroke_width=3) for c in cs])
        phi = T(r"$\varphi\colon S\to T$ may identify sorts", 0.6, DERIV_COLOR).next_to(VGroup(cs, cu), DOWN, buff=0.3)
        self.play(FadeIn(cs), FadeIn(cu), GrowArrow(arrs[0]), GrowArrow(arrs[1]), FadeIn(phi), run_time=1.4)

        self.cue(2)
        e1 = M(rf"\mathbf{{c}}^{{(n)}}\colon{N.ext()}\to{N.ext(s=LAM)},\quad {N.sc('k','s')}\mapsto\mathrm{{sc}}^{{k}}_{{\varphi(s)}}(v^{{\varphi(s)}}_{{0}})", 0.62, DERIV_COLOR)
        e2 = M(rf"\mathbf{{c}}^{{\mathrm{{htg}}(n)}}\colon{N.ext(htg=True)}\to{N.ext(htg=True, s=LAM)},\quad\varphi^{{\mathrm{{htg}}(n)}}(k,s)=(k,\varphi(s))", 0.62, DERIV_COLOR)
        VGroup(e1, e2).arrange(DOWN, aligned_edge=LEFT, buff=0.25).move_to(RIGHT * 2.3 + UP * 0.9)
        self.play(Write(e1), run_time=1.6)
        self.play(Write(e2), run_time=1.6)
        g1 = drawer_grid(rows=2, width=1.3, height=0.45).move_to(RIGHT * 0.8 + DOWN * 1.1)
        g2 = drawer_grid(rows=2, sorts=("u",), width=1.3, height=0.45).move_to(RIGHT * 4.4 + DOWN * 1.1)
        ga = Arrow(g1.get_right(), g2.get_left(), buff=0.2, color=DERIV_COLOR, stroke_width=3)
        self.play(FadeIn(g1), GrowArrow(ga), run_time=0.9)
        c1, c2 = g1[0].copy(), g1[1].copy()
        self.play(c1.animate.move_to(g2), c2.animate.move_to(g2), run_time=1.0)
        self.play(FadeOut(c1), FadeOut(c2), FadeIn(g2), run_time=0.6)

        self.cue(3)
        self.play(FadeOut(VGroup(cs, cu, arrs, phi, e1, e2, g1, g2, ga)), run_time=0.6)
        fl = M(N.cat(s=LAM), 0.75).move_to(RIGHT * 2.6 + UP * 0.9)
        fsg = M(N.cat(), 0.75).move_to(LEFT * 2.6 + UP * 0.9)
        fa = Arrow(fl.get_left(), fsg.get_right(), buff=0.2, color=FUNCTOR_COLOR, stroke_width=4)
        fal = M(r"\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}", 0.65, FUNCTOR_COLOR).next_to(fa, UP, buff=0.05)
        self.play(FadeIn(fl), FadeIn(fsg), GrowArrow(fa), Write(fal), run_time=1.2)
        split = T(r"split $\mathsf{Sig}_{\mathfrak{d}}$-indexed categories $\mathsf{nCatAlg}$, $\mathsf{nCat}^{\mathrm{htg}}\mathsf{Alg}$", 0.62).next_to(fa, DOWN, buff=0.35)
        self.play(FadeIn(split), run_time=0.8)

        self.cue(4)
        expl = T(r"a category for every signature, a functor for every derivor", 0.6, GREY_A).next_to(split, DOWN, buff=0.2)
        self.play(FadeIn(expl), run_time=0.8)

        self.cue(5)
        self.play(FadeOut(VGroup(fl, fsg, fa, fal, split, expl)), d.animate.scale(0.8).to_edge(UP, buff=0.85), run_time=0.6)
        sq = cat_square(N.cat(s=LAM), N.cat(htg=True, s=LAM), N.cat(), N.cat(htg=True), w=2.9, h=1.1, center=UP * 0.6)
        gdL = Arrow(sq[0].get_right(), sq[1].get_left(), buff=0.2, color=FUNCTOR_COLOR, stroke_width=4)
        gdS = Arrow(sq[2].get_right(), sq[3].get_left(), buff=0.2, color=FUNCTOR_COLOR, stroke_width=4)
        v1 = Arrow(sq[0].get_bottom(), sq[2].get_top(), buff=0.12, color=DERIV_COLOR, stroke_width=4)
        v2 = Arrow(sq[1].get_bottom(), sq[3].get_top(), buff=0.12, color=DERIV_COLOR, stroke_width=4)
        labs = VGroup(M(N.functor("Gd", "n", s=LAM), 0.6, FUNCTOR_COLOR).next_to(gdL, UP, buff=0.05),
                      M(N.functor("Gd", "n", s=SIG), 0.6, FUNCTOR_COLOR).next_to(gdS, DOWN, buff=0.05),
                      M(r"\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}", 0.6, DERIV_COLOR).next_to(v1, LEFT, buff=0.05),
                      M(r"\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}", 0.6, DERIV_COLOR).next_to(v2, RIGHT, buff=0.05))
        self.play(FadeIn(sq), Create(VGroup(gdL, gdS, v1, v2)), FadeIn(labs), run_time=1.4)
        eq = MathTex("=").scale(1.2).move_to(sq.get_center())
        why = M(rf"\mathbf{{c}}^{{(n)}}\circ{N.functor('Gd','n',s=SIG,bold=True)}={N.functor('Gd','n',s=LAM,bold=True)}\circ\mathbf{{c}}^{{\mathrm{{htg}}(n)}}", 0.62, DERIV_COLOR).move_to(DOWN * 1.75)
        self.play(FadeIn(eq, scale=0.5), Write(why), run_time=1.4)
        same = T(r"also for $" + N.functor("Uf", "n") + r"$, $" + N.functor("Ds", "n", "m") + r"$, $" + N.functor("Tr", "m", "n") +
                 r"$, heterogeneous, and in dimension $\omega$", 0.6, GREY_A).next_to(why, DOWN, buff=0.18)
        self.play(FadeIn(same), run_time=0.8)

        self.cue(6)
        nat = T(r"natural transformations between split indexed categories;\\they extend to the Grothendieck constructions", 0.6, FUNCTOR_COLOR).next_to(same, DOWN, buff=0.18)
        self.play(FadeIn(nat, shift=UP * 0.1), run_time=1.0)
        self.finish()


class Scene20Summary(V3Scene):
    scene_id = 20
    part = 4
    tail = 6.0
    show_progress = False

    def construct(self):
        front, back, horiz, vert, depth, back_arrows = summary_cube()
        self.add(front)
        self.play(FadeIn(front), Create(horiz), run_time=0.7)
        self.play(Create(vert), run_time=0.5)
        self.play(FadeIn(back), FadeIn(back_arrows), Create(depth), run_time=0.6)
        self.bring_to_front(front)

        self.cue(1)
        labels = [T(r"presentation", 0.6, YELLOW), T(r"dimension", 0.6, YELLOW), T(r"signature", 0.6, YELLOW)]
        labels[0].next_to(horiz[1], DOWN, buff=0.25)
        labels[1].rotate(PI / 2).move_to([-5.2, -0.1, 0])
        labels[2].next_to(depth[5], RIGHT, buff=0.15)
        for group, lab, t in zip([horiz, vert, depth], labels, [0.0, 2.6, 5.2]):
            self.cue(1, t)
            self.play(group.animate.set_color(YELLOW), FadeIn(lab), run_time=0.7)
            self.play(group.animate.set_color(FUNCTOR_COLOR if group is not depth else DERIV_COLOR), run_time=0.6)

        self.cue(2)
        uf_omega = horiz[2][1]
        others = [a for g in (horiz, vert) for pr in g for a in pr if a is not uf_omega]
        self.play(*[a.animate.set_color(DERIV_COLOR) for a in others], run_time=1.2)
        exc = M(N.functor("Uf", "omega"), 0.65, FUNCTOR_COLOR).next_to(uf_omega, DOWN, buff=0.12)
        self.play(FadeIn(exc), Indicate(uf_omega, color=FUNCTOR_COLOR), run_time=0.9)

        self.cue(3)
        mech = T(r"generalized hep-derivors", 0.85, DERIV_COLOR).to_edge(DOWN, buff=0.3)
        self.play(Write(mech), run_time=1.0)

        self.wait_until(self.voice_duration + 0.6)
        everything = VGroup(front, back, horiz, vert, depth, back_arrows, exc, mech, *labels)
        block = title_block(0.9).move_to(UP * 0.4)
        authors = Tex(AUTHORS).scale(0.45).next_to(block, DOWN, buff=0.45)
        self.play(FadeOut(everything), run_time=0.8)
        self.play(Write(block[0]), run_time=1.2)
        self.play(FadeIn(block[1]), FadeIn(authors), run_time=0.8)
        self.finish(fade=1.2)
