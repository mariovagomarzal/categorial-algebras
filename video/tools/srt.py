"""Subtitles (SRT) for the joined video, from the voice-over timings and the rendered scenes.

Usage: uv run python tools/srt.py [quality dir, default 1080p60] [output .srt]
The text is taken from the `> ` lines of script.md (before the pronunciation fixes of tts.py).
"""

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPLIT = re.compile(r"(?<=[.?!:])\s+")


def script_sentences():
    texts, scene = {}, None
    for line in (ROOT / "script.md").read_text().splitlines():
        m = re.match(r"## Scene (\d+)", line)
        if m:
            scene = int(m.group(1))
        elif line.startswith("> ") and scene is not None:
            texts[scene] = (texts.get(scene, "") + " " + line[2:]).strip()
    return {k: SPLIT.split(v) for k, v in texts.items()}


def duration(path):
    out = subprocess.run(["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", str(path)],
                         capture_output=True, text=True, check=True).stdout
    return float(out)


def stamp(t):
    ms = round(t * 1000)
    h, ms = divmod(ms, 3600_000)
    m, ms = divmod(ms, 60_000)
    s, ms = divmod(ms, 1000)
    return f"{h:02d}:{m:02d}:{s:02d},{ms:03d}"


def main(quality="1080p60", out=None):
    out = Path(out or ROOT / f"higher-order-many-sorted-categorial-algebras-{quality}.srt")
    names = re.findall(r"^class (Scene(\d+)\w+)", (ROOT / "scenes.py").read_text(), re.M)
    sentences = script_sentences()
    entries, offset = [], 0.0
    for name, num in names:
        k = int(num)
        meta = json.loads((ROOT / "voiceover" / f"scene{k:02d}.json").read_text())
        starts = [s["start"] for s in meta["sentences"]] + [meta["duration"]]
        texts = sentences[k]
        assert len(texts) == len(meta["sentences"]), f"scene {k}: sentence count differs from the voice-over"
        for i, text in enumerate(texts):
            entries.append((offset + starts[i], offset + starts[i + 1] - 0.05, text))
        offset += duration(ROOT / "media" / "videos" / "scenes" / quality / f"{name}.mp4")
    out.write_text("".join(f"{i}\n{stamp(a)} --> {stamp(b)}\n{t}\n\n" for i, (a, b, t) in enumerate(entries, 1)))
    print("wrote", out.name, f"({len(entries)} subtitles)")


if __name__ == "__main__":
    main(*sys.argv[1:])
