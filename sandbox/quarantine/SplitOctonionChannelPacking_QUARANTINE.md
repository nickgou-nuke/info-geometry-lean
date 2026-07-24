# QUARANTINED: SplitOctonionChannelPacking.lean

## Date: 2026-07-19 (re-quarantined after failed "fix" attempt)

## Reason for quarantine

File was restored and claimed "fixed" (compile lints + coordinate order), but
verification shows it is STILL BROKEN:

1. **Lean 3 syntax `<;>`** (29 occurrences) — invalid in Lean 4 (correct: `;>`)
   - `unexpected token '<;>'` at lines 75, 114, etc.
2. **Proof failures even after syntax fix would be needed**:
   - `linarith failed to find a contradiction` (lines 69, 73, 106)
   - `aesop failed, made no progress` (line 101)
   - `unsolved goals` (lines 65, 102)

The "fix" introduced Lean 3 syntax and did not resolve the underlying proof gaps.
File is NOT imported by any `All.lean`, but `lake build InfoGeometry` compiles ALL
files in the tree, so this breaks the full build.

## Status

QUARANTINED (BROKEN) - not part of `lake build InfoGeometry`.
Two copies in quarantine:
- `SplitOctonionChannelPacking.lean` (original, 5265 bytes)
- `SplitOctonionChannelPacking_BROKEN.lean` (restored+modified, 5747 bytes, has `<;>`)
