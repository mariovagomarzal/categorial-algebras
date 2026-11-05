# The video

The sources of the video that explains the paper, [published on
YouTube](https://youtu.be/yFD3TaKQ5fY). It is animated with
[Manim Community](https://www.manim.community/), and its narration was generated
with [ElevenLabs](https://elevenlabs.io/).

## Files

- `script.md`: the script, with the visuals and the voice-over of every scene.
- `scenes.py`: one Manim scene per scene of the script.
- `components.py`: the shared visuals, and `VoiceScene`, which plays a scene over
  its narration and syncs the animations to the start of its sentences.
- `notation.py`: the notation of the paper; every formula is built from it.
- `voiceover/`: the narration, `sceneNN.mp3`, with `sceneNN.json`, which holds its
  duration and the start time of each sentence. These files are committed because
  generating them needs an ElevenLabs account and does not give the same audio
  twice.
- `thumbnail.py`: the thumbnail of the video.
- `build.sh`: renders every scene, in parallel, and joins them.
- `tools/tts.py`: generates the narration from the `> ` lines of `script.md`.
- `tools/srt.py`: generates the subtitles from the timings of the narration.
- `tools/contact.py`: makes a contact sheet of a rendered scene, with one frame
  before each sentence, for reviewing it.
- `tools/lint_notation.py`: checks the notation of the script.

## Building

Building the video needs [uv](https://docs.astral.sh/uv/), FFmpeg, a LaTeX
distribution with `dvisvgm`, and the system libraries of Manim (Cairo and Pango).
These are the commands, from this directory:

```sh
./build.sh                                  # the video, at 1080p60
./build.sh l                                # a quick draft, at 480p15
uv run python tools/srt.py                  # the subtitles of the 1080p60 video
uv run python -m manim -s -qh thumbnail.py Thumbnail    # the thumbnail
uv run python -m manim -pql scenes.py Scene03CategoryAsPartialAlgebra    # one scene
uv run python tools/lint_notation.py        # the check of the notation
```

On a fresh checkout, the parallel renders can race on the empty LaTeX cache and
some scenes may fail: run `./build.sh` again, or use `JOBS=1 ./build.sh`. Run
`tools/srt.py` after `./build.sh`, since it reads the rendered scenes. The
video is written to `higher-order-many-sorted-categorial-algebras-<quality>.mp4`,
and the thumbnail to `media/images/thumbnail/`.

## Changing the narration

After editing the voice-over of a scene in `script.md`, generate its audio again
and check the `cue(i)` calls of the scene, which refer to sentence numbers:

```sh
uv run python tools/tts.py 3 7              # scenes 3 and 7; all of them by default
```

The API key is read from `~/.config/elevenlabs/api_key`. The voice is George
(`JBFqnCBsd6RMkjVDRZzb`) and the model `eleven_multilingual_v2`. The spoken forms
of symbols are in `PRONUNCIATION`, in `tools/tts.py`.
