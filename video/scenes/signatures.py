"""Signatures: the change of signature and the summary.

One Manim scene per scene of script.md; every formula follows notation.py.
"""

from components import *


class Scene19ChangeOfSignature(PartScene):
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


class Scene20Summary(PartScene):
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
