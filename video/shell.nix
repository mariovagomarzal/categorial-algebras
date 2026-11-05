# The system dependencies of the video: `nix-shell video/shell.nix` from the root of the repository.
{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  packages = with pkgs; [
    just
    uv
    ffmpeg
    # To build pycairo and ManimPango.
    pkg-config
    cairo
    pango
    meson
    ninja
    # Manim writes formulas with LaTeX and converts them with dvisvgm.
    (texliveSmall.withPackages (ps: with ps; [ standalone preview dvisvgm ]))
  ];
}
