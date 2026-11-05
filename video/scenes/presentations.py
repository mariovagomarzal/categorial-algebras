"""Presentations: the homogeneous and the heterogeneous categorial extensions, and the four functors.

One Manim scene per scene of script.md; every formula follows notation.py.
"""

from components import *


class Scene06SingleSetExtension(PartScene):
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


class Scene07HeterogeneousExtension(PartScene):
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


class Scene08FourFunctors(PartScene):
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
