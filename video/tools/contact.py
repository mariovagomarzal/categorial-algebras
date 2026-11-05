"""A contact sheet of a rendered scene, for reviewing it: one frame just before each sentence of
the narration, and one before the fade-out.

Usage: python -m tools.contact <scene number> [quality]   (l by default)
Writes build/contact/sceneNN.png.
"""

import subprocess
import sys

from PIL import Image

from tools.common import BUILD, ROOT, narration, scene_video, scenes


def main(number, quality="l"):
    number = int(number)
    (_, name, path), = [s for s in scenes() if s[0] == number]
    video = scene_video(name, path, quality)
    meta = narration(number)
    times = [s["start"] for s in meta["sentences"]][1:] + [meta["duration"] + 0.2]
    out = BUILD / "contact" / f"scene{number:02d}.png"
    out.parent.mkdir(parents=True, exist_ok=True)
    frames = []
    for i, t in enumerate(times):
        frame = out.with_suffix(f".{i}.png")
        subprocess.run(["ffmpeg", "-v", "error", "-y", "-ss", f"{max(t - 0.1, 0):.2f}", "-i", str(video),
                        "-frames:v", "1", str(frame)], check=True)
        frames.append(Image.open(frame))
        frame.unlink()
    w, h = frames[0].size
    cols = 2 if len(frames) > 1 else 1
    rows = (len(frames) + cols - 1) // cols
    sheet = Image.new("RGB", (cols * w, rows * h), "grey")
    for i, f in enumerate(frames):
        sheet.paste(f, ((i % cols) * w, (i // cols) * h))
    sheet.save(out)
    print("wrote", out.relative_to(ROOT))


if __name__ == "__main__":
    main(*sys.argv[1:])
