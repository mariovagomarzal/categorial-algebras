#!/usr/bin/env bash
# Render every scene and join them into a single video.
# Usage: ./build.sh [l|m|h|k]   (Manim quality, default h = 1080p60)
set -euo pipefail
cd "$(dirname "$0")"
Q="${1:-h}"
UV="$(command -v uv || echo "$HOME/.local/bin/uv")"
SCENES=$(grep -oE '^class Scene[0-9]+\w+' scenes.py | cut -d' ' -f2)

# Render the voice-over padding once, before the parallel renders race for it.
"$UV" run python -c "import components" 2>/dev/null
# Parallel renders can race on the shared LaTeX cache, so a failed scene is retried once.
RENDER="'$UV' run python -m manim -q$Q --progress_bar none scenes.py"
printf '%s\n' $SCENES | xargs -P "${JOBS:-4}" -I{} sh -c \
  "$RENDER {} >/dev/null 2>logs_{}.txt || { sleep 2; $RENDER {} >/dev/null 2>logs_{}.txt; } && rm logs_{}.txt || { echo 'failed: {} (see logs_{}.txt)'; exit 1; }"

case "$Q" in l) DIR=480p15;; m) DIR=720p30;; h) DIR=1080p60;; k) DIR=2160p60;; esac
LIST=$(mktemp)
for s in $SCENES; do echo "file '$PWD/media/videos/scenes/$DIR/$s.mp4'" >> "$LIST"; done
OUT="higher-order-many-sorted-categorial-algebras-$DIR.mp4"
ffmpeg -v error -y -f concat -safe 0 -i "$LIST" -c:v libx264 -preset medium -crf 18 -pix_fmt yuv420p \
  -af loudnorm=I=-16:TP=-1.5:LRA=11 -c:a aac -b:a 192k -ar 44100 -movflags +faststart "$OUT"
rm "$LIST"
echo "wrote $OUT ($(ffprobe -v error -show_entries format=duration -of csv=p=0 "$OUT") s)"
