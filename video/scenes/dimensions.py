"""Dimensions: graduation, unification, discretization, truncation, the algebraic square and dimension omega.

One Manim scene per scene of script.md; every formula follows notation.py.
"""

from components import *


def bags_and_grid(bag_x=-4.6, grid_x=3.4, y=-0.6, rows=3):
    As = sort_bag("s", r"\mathsf{A}_s", 1.9, 1.3, dims=(0, 1, 2)).move_to(np.array([bag_x, y + 0.9, 0]))
    At = sort_bag("t", r"\mathsf{A}_t", 1.9, 1.3, dims=(0, 1)).move_to(np.array([bag_x, y - 1.0, 0]))
    cols = drawer_grid(rows=rows, width=1.9, height=0.6, top="n").move_to(np.array([grid_x, y, 0]))
    return As, At, cols


class Scene13Graduation(PartScene):
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


class Scene14Unification(PartScene):
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


class Scene15DiscretizationTruncation(PartScene):
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


class Scene16AlgebraicSquare(PartScene):
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


class Scene17DimensionOmega(PartScene):
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


class Scene18UnificationOmega(PartScene):
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
