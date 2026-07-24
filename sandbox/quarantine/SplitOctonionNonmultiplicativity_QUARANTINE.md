# QUARANTINED: SplitOctonionNonmultiplicativity.lean

## Date: 2026-07-19 (created 19:57, after user's build report)

## Reason for quarantine

File created AFTER the user's "green build" report. It is BROKEN:
- References non-existent namespaces: `InfoGeometry.Lie.SplitOctonionCliffordAction`,
  `InfoGeometry.Canonical.ZornSpinor`
- Uses Lean 3 syntax `<;>` (invalid in Lean 4)
- Unknown identifiers: `upper`, `e0`, `ZornMatrix`
- NOT imported by any `All.lean`, but `lake build InfoGeometry` compiles all files
  in the tree, so it breaks the full build.

## Status
QUARANTINED (BROKEN) - not part of `lake build InfoGeometry`.
