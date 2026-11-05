"""Paths and scenes of the video, shared by the tools."""

import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
MEDIA = BUILD / "media"
VOICEOVER = ROOT / "voiceover"
# The stem of every file of the published video: the video, its subtitles and its poster.
NAME = "categorial-algebras"
# The output folder of Manim for each quality.
QUALITIES = {"l": "480p15", "m": "720p30", "h": "1080p60", "k": "2160p60"}


def scenes():
    """The scenes of the video in order, as (number, class name, module path)."""
    found = []
    for path in (ROOT / "scenes").glob("*.py"):
        for m in re.finditer(r"^class (Scene(\d+)\w*)\(", path.read_text(), re.M):
            found.append((int(m.group(2)), m.group(1), path))
    return sorted(found)


def scene_video(name, path, quality):
    """The rendered video of a scene."""
    return MEDIA / "videos" / path.stem / QUALITIES[quality] / f"{name}.mp4"


def narration(number):
    """The timings of the narration of a scene: its duration and the start of each sentence."""
    return json.loads((VOICEOVER / f"scene{number:02d}.json").read_text())


def duration(path):
    """The duration of a media file, in seconds."""
    out = subprocess.run(["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", str(path)],
                         capture_output=True, text=True, check=True).stdout
    return float(out)
