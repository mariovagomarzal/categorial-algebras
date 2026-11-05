"""Shared building blocks for the higher-order categorial algebras video."""

import json
import subprocess
from pathlib import Path

from manim import *

ROOT = Path(__file__).resolve().parent

# Macros of the paper used in formulas (main.tex: \calg for categorial algebras).
_template = TexTemplate()
_template.add_to_preamble(r"\newcommand{\calg}[1]{\boldsymbol{\mathsf{#1}}}")
config.tex_template = _template
VOICEOVER = ROOT / "voiceover"

DIM_COLORS = [WHITE, BLUE, YELLOW]
OP_COLOR = GREEN
FUNCTOR_COLOR = ORANGE
ID_COLOR = GREY_B
BAG_COLOR = "#7A8CB8"
DRAWER_COLOR = "#B89A6E"
DERIV_COLOR = "#4FD1C5"  # derivors, domains and their filters


class VoiceScene(Scene):
    """A scene played over its voice-over track.

    `cue(i)` waits until sentence i of the narration starts, so animations stay
    in sync with the voice whatever the length of the previous ones.
    """

    scene_id = 0
    tail = 1.0  # seconds of silence after the narration, including the fade-out

    def setup(self):
        meta = json.loads((VOICEOVER / f"scene{self.scene_id:02d}.json").read_text())
        self.voice_cues = [s["start"] for s in meta["sentences"]]
        self.voice_duration = meta["duration"]
        # Manim cuts the video to the length of its audio, so pad the narration
        # with silence to cover the tail.
        padded = VOICEOVER / "padded" / f"scene{self.scene_id:02d}.wav"
        source = VOICEOVER / f"scene{self.scene_id:02d}.mp3"
        if not padded.exists() or padded.stat().st_mtime < source.stat().st_mtime:
            padded.parent.mkdir(exist_ok=True)
            subprocess.run(["ffmpeg", "-v", "error", "-y", "-i", str(source), "-af",
                            f"apad=pad_dur={self.tail}", str(padded)], check=True)
        self.add_sound(str(padded))

    def now(self):
        return self.renderer.time

    def wait_until(self, t):
        if t - self.now() > 1 / 30:
            self.wait(t - self.now())

    def cue(self, i, offset=0.0):
        self.wait_until(self.voice_cues[i] + offset)

    def finish(self, fade=0.7):
        self.wait_until(self.voice_duration + self.tail - fade)
        if self.mobjects:
            self.play(*[FadeOut(m) for m in self.mobjects], run_time=fade)
        self.wait_until(self.voice_duration + self.tail)


def heading(text):
    return Tex(text).scale(0.9).to_edge(UP, buff=0.4)


def caption(text, scale=0.7):
    return Tex(text).scale(scale).to_edge(DOWN, buff=0.45)


def obj(label, point, label_dir=DOWN):
    """A 0-cell: a white dot with a label."""
    dot = Dot(point, radius=0.08, color=DIM_COLORS[0])
    tex = MathTex(label).scale(0.8).next_to(dot, label_dir, buff=0.15)
    return VGroup(dot, tex)


def mor(start, end, label=None, angle=0.0, color=DIM_COLORS[1], label_dir=UP, buff=0.18):
    """A 1-cell from `start` to `end`, optionally curved, with a label."""
    direction = normalize(end - start)
    a, b = start + direction * buff, end - direction * buff
    if angle:
        arrow = CurvedArrow(a, b, angle=angle, color=color, stroke_width=4, tip_length=0.2)
    else:
        arrow = Arrow(a, b, buff=0, color=color, stroke_width=4, max_tip_length_to_length_ratio=0.15)
    group = VGroup(arrow)
    if label:
        tex = MathTex(label, color=color).scale(0.7)
        tex.next_to(arrow.point_from_proportion(0.5), label_dir, buff=0.1)
        group.add(tex)
    return group


def two_cell(top, bottom, label=None, color=DIM_COLORS[2]):
    """A 2-cell drawn between the midpoints of two parallel 1-cells."""
    p, q = top[0].point_from_proportion(0.5), bottom[0].point_from_proportion(0.5)
    arrow = MathTex(r"\Downarrow", color=color).scale(0.9)
    arrow.stretch_to_fit_height(max(0.3, 0.55 * (p[1] - q[1])))
    arrow.move_to((p + q) / 2)
    group = VGroup(arrow)
    if label:
        group.add(MathTex(label, color=color).scale(0.7).next_to(arrow, RIGHT, buff=0.08))
    return group


def op_box(symbol, color=OP_COLOR, size=0.9):
    box = RoundedRectangle(corner_radius=0.15, width=size, height=size, color=color)
    box.set_fill(color, opacity=0.15)
    return VGroup(box, MathTex(symbol, color=color).scale(0.9))


def glyph(dim, identity=False):
    """A small icon for a cell of the given dimension."""
    color = ID_COLOR if identity else DIM_COLORS[dim]
    if dim == 0:
        return Dot(radius=0.07, color=color)
    if dim == 1:
        return Arrow(LEFT * 0.22, RIGHT * 0.22, buff=0, color=color, stroke_width=3,
                     max_tip_length_to_length_ratio=0.35)
    return MathTex(r"\Downarrow", color=color).scale(0.7)


def bag(width=3.4, height=2.4, label=None):
    shape = Ellipse(width=width, height=height, color=BAG_COLOR)
    shape.set_fill(BAG_COLOR, opacity=0.12)
    group = VGroup(shape)
    if label:
        group.add(MathTex(label, color=BAG_COLOR).scale(0.8).next_to(shape, UP, buff=0.1))
    return group


# Positions (relative to the bag centre) of a mixed bag of cells, with their dimensions.
BAG_LAYOUT = [
    (0, [-1.1, 0.4, 0]), (0, [0.2, 0.75, 0]), (0, [1.0, -0.2, 0]), (0, [-0.3, -0.7, 0]),
    (1, [-0.4, 0.15, 0]), (1, [0.75, 0.45, 0]), (1, [-1.0, -0.35, 0]), (1, [0.35, -0.45, 0]),
    (2, [0.15, -0.05, 0]), (2, [1.2, 0.3, 0]), (2, [-0.75, 0.75, 0]),
]


def bag_cells(center, dims=None):
    cells = VGroup()
    for dim, pos in BAG_LAYOUT:
        if dims is None or dim in dims:
            g = glyph(dim).move_to(np.array(center) + np.array(pos))
            g.cell_dim = dim
            cells.add(g)
    return cells


def drawers(n=3, width=3.2, height=0.9):
    """Stacked drawers C_0 (bottom) ... C_{n-1} (top) of the extended presentation."""
    group = VGroup()
    for k in range(n):
        rect = Rectangle(width=width, height=height, color=DRAWER_COLOR)
        rect.set_fill(DRAWER_COLOR, opacity=0.1)
        tex = MathTex(f"C_{k}", color=DRAWER_COLOR).scale(0.75)
        tex.move_to(rect.get_left() + RIGHT * 0.35)
        group.add(VGroup(rect, tex))
    group.arrange(UP, buff=0.35)
    return group


def drawer_slots(drawer, count):
    """`count` evenly spaced points inside a drawer, right of its label."""
    rect = drawer[0]
    left = rect.get_left() + RIGHT * 0.9
    right = rect.get_right() + LEFT * 0.35
    return [left + (right - left) * (i + 0.5) / count for i in range(count)]


def adj_pair(start, end, upper, lower, horizontal=True, gap=0.17, symbol=True, scale=0.65):
    """A pair of opposite functor arrows with an adjunction symbol between them.

    `upper` labels the arrow from `start` to `end`; `lower` the way back.
    For a horizontal pair the left adjoint is drawn on top; for a vertical pair
    the left adjoint is the downward arrow on the right.
    """
    side = UP if horizontal else RIGHT
    there = Arrow(start + side * gap, end + side * gap, buff=0, color=FUNCTOR_COLOR,
                  stroke_width=4, max_tip_length_to_length_ratio=0.08)
    back = Arrow(end - side * gap, start - side * gap, buff=0, color=FUNCTOR_COLOR,
                 stroke_width=4, max_tip_length_to_length_ratio=0.08)
    l1 = MathTex(upper, color=FUNCTOR_COLOR).scale(scale).next_to(there, side, buff=0.08)
    l2 = MathTex(lower, color=FUNCTOR_COLOR).scale(scale).next_to(back, -side, buff=0.08)
    sym = MathTex(r"\dashv").scale(0.7).move_to((start + end) / 2)
    sym.rotate(-PI / 2 if horizontal else PI)
    if not symbol:
        sym.set_opacity(0)
    return VGroup(there, back, l1, l2, sym)


def tower(levels, spacing=1.15, width=2.6):
    """A vertical tower of labelled boxes, bottom to top."""
    group = VGroup()
    for tex in levels:
        label = MathTex(tex).scale(0.7)
        box = RoundedRectangle(corner_radius=0.12, width=width, height=0.65, color=GREY_B)
        group.add(VGroup(box, label))
    group.arrange(UP, buff=spacing - 0.65)
    return group


def gate(label, width=3.6, color=DERIV_COLOR):
    """A domain filter: a dashed bar with the existence equations that a cell must satisfy."""
    bar = DashedLine(LEFT * width / 2, RIGHT * width / 2, color=color, stroke_width=5, dash_length=0.12)
    tex = MathTex(label, color=color).scale(0.7).next_to(bar, RIGHT, buff=0.2)
    return VGroup(bar, tex)


def sig_box(label, width=1.5, height=1.0, color=GREY_B):
    box = RoundedRectangle(corner_radius=0.15, width=width, height=height, color=color)
    box.set_fill(color, opacity=0.08)
    return VGroup(box, MathTex(label).scale(0.9).move_to(box))


def check_item(text, color=GREEN):
    mark = MathTex(r"\checkmark", color=color).scale(0.8)
    tex = Tex(text).scale(0.6)
    return VGroup(mark, tex).arrange(RIGHT, buff=0.2)


def cat_square(tl, tr, bl, br, w=3.2, h=1.7, scale=0.7, center=ORIGIN):
    """Four category labels at the corners of a rectangle."""
    pts = [UL, UR, DL, DR]
    labels = VGroup(*[MathTex(t).scale(scale) for t in (tl, tr, bl, br)])
    for lab, p in zip(labels, pts):
        lab.move_to(np.array(center) + np.array([p[0] * w, p[1] * h, 0]))
    return labels


def square_arrows(labels, gd=r"\mathrm{Gd}", uf=r"\mathrm{Uf}", ds=r"\mathrm{Ds}", tr=r"\mathrm{Tr}", symbol=True, scale=0.65):
    """Gd/Uf pairs on the horizontal sides, Ds/Tr pairs on the vertical sides of `cat_square`."""
    tl, tr_, bl, br = labels
    top = adj_pair(tl.get_right() + RIGHT * 0.2, tr_.get_left() + LEFT * 0.2, gd, uf, symbol=symbol, scale=scale)
    bot = adj_pair(bl.get_right() + RIGHT * 0.2, br.get_left() + LEFT * 0.2, gd, uf, symbol=symbol, scale=scale)
    left = adj_pair(tl.get_bottom() + DOWN * 0.15, bl.get_top() + UP * 0.15, ds, tr, horizontal=False, symbol=symbol, scale=scale)
    right = adj_pair(tr_.get_bottom() + DOWN * 0.15, br.get_top() + UP * 0.15, ds, tr, horizontal=False, symbol=symbol, scale=scale)
    return top, bot, left, right


# ---------------------------------------------------------------------------
# Sorts, grids of drawers, two levels, recap cards and progress bar.
# ---------------------------------------------------------------------------

SORT_COLORS = {"s": "#7A8CB8", "t": "#B87A9C", "u": "#8FB87A", "w": "#B8A97A"}
DIM3_COLOR = "#B39DDB"
STRUCT_COLOR = GREY_B
PARTS = ["algebras", "presentations", "hep-derivors", "dimensions", "signatures"]


def T(text, scale=0.65, color=WHITE):
    """Text with the minimum readable size."""
    return Tex(text, color=color).scale(max(scale, 0.6))


def M(tex, scale=0.75, color=WHITE):
    """A formula with the minimum readable size."""
    return MathTex(tex, color=color).scale(max(scale, 0.65))


def progress_bar(part):
    """The five parts of the video at the bottom of the screen, the current one highlighted."""
    items = VGroup(*[Tex(p, color=WHITE if i == part else GREY_D).scale(0.42) for i, p in enumerate(PARTS)])
    items.arrange(RIGHT, buff=0.5).to_edge(DOWN, buff=0.12)
    line = Line(items.get_left() + LEFT * 0.2, items.get_right() + RIGHT * 0.2, color=GREY_D, stroke_width=1)
    line.next_to(items, UP, buff=0.06)
    return VGroup(line, items)


def recap_card(lines, title="so far"):
    body = VGroup(*[Tex(r"$\cdot$ " + l).scale(0.5) for l in lines]).arrange(DOWN, aligned_edge=LEFT, buff=0.1)
    head = Tex(title, color=YELLOW).scale(0.5)
    content = VGroup(head, body).arrange(DOWN, aligned_edge=LEFT, buff=0.15)
    box = SurroundingRectangle(content, color=GREY_C, buff=0.18, corner_radius=0.1)
    box.set_fill(BLACK, opacity=0.9)
    return VGroup(box, content)


def cell_glyph(dim, identity=False, scale=1.0):
    """A cell of dimension 0, 1, 2 or 3; identities are grey."""
    if dim == 3:
        g = MathTex(r"\Rrightarrow", color=ID_COLOR if identity else DIM3_COLOR).scale(0.7)
    else:
        g = glyph(dim, identity)
    g.scale(scale)
    g.cell_dim = dim
    return g


def sort_bag(sort, label, width=2.6, height=1.9, dims=(0, 0, 0, 1, 1, 1, 2, 2), scale=1.0):
    """A bag for one sort, with its cells placed on a tidy grid by dimension."""
    color = SORT_COLORS[sort]
    shape = Ellipse(width=width, height=height, color=color).set_fill(color, opacity=0.15)
    lab = MathTex(label, color=color).scale(0.7).next_to(shape, UP, buff=0.08)
    cells = VGroup()
    rows = {}
    for d in dims:
        rows.setdefault(d, 0)
        rows[d] += 1
    for d, count in rows.items():
        for i in range(count):
            g = cell_glyph(d, scale=scale)
            g.move_to(shape.get_center() + np.array([(i - (count - 1) / 2) * 0.5 * width / 2.6,
                                                     (len(rows) / 2 - 0.5 - d) * 0.45 * height / 1.9, 0]))
            cells.add(g)
    return VGroup(shape, lab, cells)


def drawer_grid(rows=3, sorts=("s", "t"), width=1.9, height=0.62, label=True, gap=0.22, top=None):
    """Drawers A_{(k,s)}: one column per sort, one row per dimension (row 0 at the bottom)."""
    grid = VGroup()
    cols = VGroup()
    for s in sorts:
        col = VGroup()
        for k in range(rows):
            rect = Rectangle(width=width, height=height, color=SORT_COLORS[s]).set_fill(SORT_COLORS[s], opacity=0.1)
            parts = [rect]
            if label:
                kk = top if (top is not None and k == rows - 1) else k
                parts.append(MathTex(rf"({kk},{s})", color=SORT_COLORS[s]).scale(0.5).move_to(rect.get_left() + RIGHT * 0.38))
            drawer = VGroup(*parts)
            drawer.sort_name, drawer.k = s, k
            col.add(drawer)
        col.arrange(UP, buff=gap)
        cols.add(col)
    cols.arrange(RIGHT, buff=0.35)
    grid.add(cols)
    return cols


def slots(drawer, count, left=0.75):
    rect = drawer[0]
    a = rect.get_left() + RIGHT * left
    b = rect.get_right() + LEFT * 0.25
    return [a + (b - a) * (i + 0.5) / count for i in range(count)]


def two_levels(derivor, functor, width=5.0, center=ORIGIN, left_to_right=True):
    """A derivor between signatures (teal, above) and the functor it induces (orange, below, reversed)."""
    d = 1 if left_to_right else -1
    top = Arrow(LEFT * width / 2 * d, RIGHT * width / 2 * d, buff=0, color=DERIV_COLOR, stroke_width=4,
                max_tip_length_to_length_ratio=0.06)
    bot = Arrow(RIGHT * width / 2 * d, LEFT * width / 2 * d, buff=0, color=FUNCTOR_COLOR, stroke_width=5,
                max_tip_length_to_length_ratio=0.06)
    top.shift(UP * 0.55)
    bot.shift(DOWN * 0.55)
    tl = MathTex(derivor, color=DERIV_COLOR).scale(0.7).next_to(top, UP, buff=0.1)
    bl = MathTex(functor, color=FUNCTOR_COLOR).scale(0.7).next_to(bot, DOWN, buff=0.1)
    note = Tex(r"the functor goes against the derivor", color=GREY_B).scale(0.5)
    return VGroup(top, tl, bot, bl).move_to(center), note


def framed(mob, color=GREEN, buff=0.2):
    return VGroup(SurroundingRectangle(mob, color=color, buff=buff, corner_radius=0.08), mob)
