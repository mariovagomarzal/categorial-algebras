"""Thumbnail of the video: uv run python -m manim -s -qh thumbnail.py Thumbnail"""

from scenes import *


class Thumbnail(Scene):
    def construct(self):
        front, back, horiz, vert, depth, back_arrows = summary_cube()
        cube = VGroup(back, back_arrows, horiz, vert, depth, front)
        for g in (horiz, vert):
            g.set_color(DERIV_COLOR)
        cube.scale(0.62).to_edge(RIGHT, buff=0.3).shift(DOWN * 0.3)
        title = Tex(r"Higher-order\\many-sorted\\categorial algebras", tex_environment="flushleft").scale(1.25)
        sub = Tex(r"via generalized\\hep-derivors", tex_environment="flushleft", color=DERIV_COLOR).scale(1.0)
        text = VGroup(title, sub).arrange(DOWN, aligned_edge=LEFT, buff=0.45).to_edge(LEFT, buff=0.6)
        self.add(cube, text)
