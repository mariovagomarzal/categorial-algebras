"""Generalized hep-derivors: derivors, their obstacles, the generalization and its lax composition.

One Manim scene per scene of script.md; every formula follows notation.py.
"""

from components import *


class Scene09Derivors(PartScene):
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


class Scene10Obstacles(PartScene):
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


class Scene11GeneralizedHepDerivors(PartScene):
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


class Scene12LaxComposition(PartScene):
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
