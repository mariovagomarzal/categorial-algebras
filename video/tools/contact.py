"""Contact sheet of a rendered scene: one frame just before each voice cue and before the fade-out."""

import json
import subprocess
import sys
from pathlib import Path

from PIL import Image

ROOT = Path(__file__).resolve().parent.parent


def main(scene_id, video, out):
    meta = json.loads((ROOT / "voiceover" / f"scene{scene_id:02d}.json").read_text())
    cues = [s["start"] for s in meta["sentences"]][1:] + [meta["duration"] + 0.2]
    frames = []
    for i, t in enumerate(cues):
        path = Path(out).with_suffix(f".{i}.png")
        subprocess.run(["ffmpeg", "-v", "error", "-y", "-ss", f"{max(t - 0.1, 0):.2f}", "-i", video,
                        "-frames:v", "1", str(path)], check=True)
        frames.append(Image.open(path))
    w, h = frames[0].size
    cols = 2 if len(frames) > 1 else 1
    rows = (len(frames) + cols - 1) // cols
    sheet = Image.new("RGB", (cols * w, rows * h), "grey")
    for i, f in enumerate(frames):
        sheet.paste(f, ((i % cols) * w, (i // cols) * h))
    sheet.save(out)
    for p in Path(out).parent.glob(Path(out).stem + ".*.png"):
        p.unlink()


if __name__ == "__main__":
    main(int(sys.argv[1]), sys.argv[2], sys.argv[3])
