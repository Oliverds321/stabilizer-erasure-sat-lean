# OpenAI's verified SAT solver (openai/math at `4eaee875`)

| Path | Contents |
|---|---|
| `NOTICE` | origin, licence and the kind of modifications |
| `modified/` | the 108 modified Lean files (21 proof-internal refactors, 87 import-only edits) |
| `upstream-manifest.json` | the 2569 upstream files of the import closure: path, git blob SHA-1, SHA-256, size, imports |
| `overlay-manifest.json` | for each of those files: upstream SHA-256, SHA-256 of the file actually compiled, kind of change |
| `records/` | the two diffs against upstream, the pinned dependency revisions and the upstream archive README |

To reconstruct the compiled solver sources:

    python -I scripts/fetch_openai_math.py --out DIR

This downloads `https://codeload.github.com/openai/math/tar.gz/4eaee87548250b2682affda7d05d947c05554bae`,
checks every file of the closure against `upstream-manifest.json`, writes
`DIR/upstream/` and `DIR/overlay/` (upstream with `modified/` applied), and checks
`DIR/overlay/` against `overlay-manifest.json`. With `--source CHECKOUT` it uses an
existing checkout of the repository at that commit instead of downloading.
