"""Render the scenes of the video, in parallel, and join them, with their subtitles.

Usage: python -m tools.build [quality] [scene numbers...]
The quality is l (480p15), m (720p30), h (1080p60, the default) or k (2160p60). With scene
numbers, only those scenes are rendered; otherwise all of them are, and joined into
build/<NAME>.mp4. JOBS sets the number of parallel renders (4 by default).
"""

import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

from tools import subtitles
from tools.common import BUILD, MEDIA, NAME, QUALITIES, ROOT, duration, scene_video, scenes


def render(scene, quality):
    """Render one scene, with a LaTeX cache of its own; return its name if it fails."""
    _, name, path = scene
    log = BUILD / "logs" / f"{name}.txt"
    log.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, VIDEO_TEX_DIR=str(BUILD / "tex" / name))
    with log.open("w") as out:
        result = subprocess.run([sys.executable, "-m", "manim", f"-q{quality}", "--progress_bar", "none",
                                 "--media_dir", str(MEDIA), str(path.relative_to(ROOT)), name],
                                cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        return name
    log.unlink()
    print("rendered", name, flush=True)


def join(quality):
    """Join the rendered scenes into one video, with its loudness normalized."""
    listing = BUILD / "scenes.txt"
    listing.write_text("".join(f"file '{scene_video(name, path, quality)}'\n" for _, name, path in scenes()))
    out = BUILD / f"{NAME}.mp4"
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-f", "concat", "-safe", "0", "-i", str(listing),
                    "-c:v", "libx264", "-preset", "medium", "-crf", "18", "-pix_fmt", "yuv420p",
                    "-af", "loudnorm=I=-16:TP=-1.5:LRA=11", "-c:a", "aac", "-b:a", "192k", "-ar", "44100",
                    "-movflags", "+faststart", str(out)], check=True)
    listing.unlink()
    print(f"wrote build/{out.name} ({duration(out):.1f} s, {out.stat().st_size / 2**20:.0f} MiB)")


def main(quality="h", *numbers):
    if quality not in QUALITIES:
        sys.exit(f"unknown quality {quality!r}: use one of {', '.join(QUALITIES)}")
    wanted = [s for s in scenes() if not numbers or s[0] in map(int, numbers)]
    with ThreadPoolExecutor(int(os.environ.get("JOBS", 4))) as pool:
        failed = [f for f in pool.map(lambda s: render(s, quality), wanted) if f]
    if failed:
        sys.exit("failed: " + ", ".join(f"{f} (see build/logs/{f}.txt)" for f in failed))
    if numbers:
        for _, name, path in wanted:
            print(scene_video(name, path, quality).relative_to(ROOT))
        return
    join(quality)
    subtitles.main(quality)


if __name__ == "__main__":
    main(*sys.argv[1:])
