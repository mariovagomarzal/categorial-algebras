"""Algebras: signatures, partial algebras, n-categories and categorial algebras.

One Manim scene per scene of script.md; every formula follows notation.py.
"""

from components import *


class Scene01Opening(PartScene):
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


class Scene02Signatures(PartScene):
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


class Scene03CategoryAsPartialAlgebra(PartScene):
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


class Scene04SingleSetNCategories(PartScene):
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


class Scene05CategorialAlgebras(PartScene):
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
