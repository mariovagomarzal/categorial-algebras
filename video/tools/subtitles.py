"""The subtitles of the joined video, from the timings of the narration and the rendered scenes.

The text is that of the `> ` lines of script.md, before the pronunciation fixes of tools/tts.py.
Writes build/<NAME>.srt and build/<NAME>.vtt.
"""

import re
import sys

from tools.common import BUILD, NAME, ROOT, duration, narration, scene_video, scenes

SPLIT = re.compile(r"(?<=[.?!:])\s+")


def script_sentences():
    """The sentences of the narration of each scene, from script.md."""
    texts, scene = {}, None
    for line in (ROOT / "script.md").read_text().splitlines():
        m = re.match(r"## Scene (\d+)", line)
        if m:
            scene = int(m.group(1))
        elif line.startswith("> ") and scene is not None:
            texts[scene] = (texts.get(scene, "") + " " + line[2:]).strip()
    return {k: SPLIT.split(v) for k, v in texts.items()}


def stamp(t, sep):
    ms = round(t * 1000)
    h, ms = divmod(ms, 3600_000)
    m, ms = divmod(ms, 60_000)
    s, ms = divmod(ms, 1000)
    return f"{h:02d}:{m:02d}:{s:02d}{sep}{ms:03d}"


def cues(quality):
    """(start, end, text) of every subtitle of the joined video."""
    sentences = script_sentences()
    entries, offset = [], 0.0
    for number, name, path in scenes():
        meta = narration(number)
        starts = [s["start"] for s in meta["sentences"]] + [meta["duration"]]
        texts = sentences[number]
        assert len(texts) == len(meta["sentences"]), f"scene {number}: sentence count differs from the narration"
        for i, text in enumerate(texts):
            entries.append((offset + starts[i], offset + starts[i + 1] - 0.05, text))
        offset += duration(scene_video(name, path, quality))
    return entries


def main(quality="h"):
    entries = cues(quality)
    srt = "".join(f"{i}\n{stamp(a, ',')} --> {stamp(b, ',')}\n{t}\n\n" for i, (a, b, t) in enumerate(entries, 1))
    vtt = "WEBVTT\n\n" + "".join(f"{stamp(a, '.')} --> {stamp(b, '.')}\n{t}\n\n" for a, b, t in entries)
    (BUILD / f"{NAME}.srt").write_text(srt)
    (BUILD / f"{NAME}.vtt").write_text(vtt)
    print(f"wrote build/{NAME}.srt and build/{NAME}.vtt ({len(entries)} subtitles)")


if __name__ == "__main__":
    main(*sys.argv[1:])
