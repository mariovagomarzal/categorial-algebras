"""Generate the voice-over for every scene of script.md with ElevenLabs.

Usage: uv run python tools/tts.py [scene numbers...]
The API key is read from ~/.config/elevenlabs/api_key.
"""

import base64
import json
import re
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "voiceover"
VOICE_ID = "JBFqnCBsd6RMkjVDRZzb"  # George: warm, calm narrator
MODEL_ID = "eleven_multilingual_v2"

# Spoken forms for symbols that text-to-speech would otherwise mangle.
PRONUNCIATION = {
    "QE-equations": "Q E equations",
    "hep-derivors": "H E P derivors",
    "hep-derivor": "H E P derivor",
    "a hep-signature": "an H E P signature",
    "an ep-algebra": "an E P algebra",
    "ep-algebras": "E P algebras",
    "ep-algebra": "E P algebra",
    "hep-signature": "H E P signature",
    "simply n category": "simply N category",
    "dimension m is": "dimension M is",
    "dimension k,": "dimension K,",
    "For n equal": "For N equal",
}
# One-letter dimensions before a hyphen (n-category, k-source, m-cells, ...).
DIMENSION = re.compile(r"(?<![A-Za-z])([nmk])-(?=[a-z])")
# Isolated one-letter dimensions ("dimension k below n", "from n to m").
LETTER = re.compile(r"(?<![A-Za-z'\-])([nmk])(?![A-Za-z'\-])")


def scene_texts():
    texts, scene = {}, None
    for line in (ROOT / "script.md").read_text().splitlines():
        m = re.match(r"## Scene (\d+)", line)
        if m:
            scene = int(m.group(1))
        elif line.startswith("> ") and scene is not None:
            texts[scene] = (texts.get(scene, "") + " " + line[2:]).strip()
    for k, v in texts.items():
        for a, b in PRONUNCIATION.items():
            v = v.replace(a, b)
        v = DIMENSION.sub(lambda m: m.group(1).upper() + " ", v)
        v = LETTER.sub(lambda m: m.group(1).upper(), v)
        texts[k] = v
    return texts


def sentence_starts(text, alignment):
    """Start time (s) of every sentence, from the character-level alignment."""
    chars, starts = alignment["characters"], alignment["character_start_times_seconds"]
    spoken = "".join(chars)
    times, pos = [], 0
    for sentence in re.split(r"(?<=[.?!:])\s+", text):
        i = spoken.find(sentence[:12], pos)
        if i < 0:
            continue
        times.append({"start": starts[i], "text": sentence})
        pos = i + 1
    return times


def synthesize(text, previous_text, next_text, path):
    key = Path("~/.config/elevenlabs/api_key").expanduser().read_text().strip()
    body = {
        "text": text,
        "model_id": MODEL_ID,
        "previous_text": previous_text,
        "next_text": next_text,
        "voice_settings": {"stability": 0.55, "similarity_boost": 0.75, "style": 0.15},
    }
    req = urllib.request.Request(
        f"https://api.elevenlabs.io/v1/text-to-speech/{VOICE_ID}/with-timestamps?output_format=mp3_44100_128",
        data=json.dumps(body).encode(),
        headers={"xi-api-key": key, "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req) as r:
        data = json.load(r)
    path.write_bytes(base64.b64decode(data["audio_base64"]))
    alignment = data["alignment"]
    path.with_suffix(".json").write_text(json.dumps({
        "duration": alignment["character_end_times_seconds"][-1],
        "sentences": sentence_starts(text, alignment),
    }, indent=2, ensure_ascii=False))


def main():
    texts = scene_texts()
    wanted = [int(a) for a in sys.argv[1:]] or sorted(texts)
    OUT.mkdir(exist_ok=True)
    (OUT / "texts.json").write_text(json.dumps(texts, indent=2, ensure_ascii=False))
    for k in wanted:
        path = OUT / f"scene{k:02d}.mp3"
        synthesize(texts[k], texts.get(k - 1, ""), texts.get(k + 1, ""), path)
        print("wrote", path.name)


if __name__ == "__main__":
    main()
