# `PrimitiveSetsAboveX` — module-directory placeholder

This directory exists so that the `lean_lib PrimitiveSetsAboveX` declaration in
`lakefile.lean` can resolve its `.andSubmodules \`PrimitiveSetsAboveX` glob
during Lake job computation. Lake enumerates `lean/PrimitiveSetsAboveX/` as the
submodule directory for the glob; without this directory, full-workspace builds
fail with `error: no such file or directory (error code: 2)` at
`Running job computation`.

There are intentionally **no** `.lean` files here:

- The library's only module is the compatibility root
  `lean/PrimitiveSetsAboveX.lean`, a symlink to
  `external/Erdos1196/PrimitiveSetsAboveX.lean` (the pinned local clone of the
  formal Lean proof of Erdős Problem #1196; theorem
  `PrimitiveSetsAboveX.mainTheorem`).
- That root is metadata-only (`PrimitiveSetsAboveX.proofPin`) and asserts no
  local axioms. See `lean/InfoGeometry/Arithmetic/Erdos1196ProofPin.lean` for
  the proof-pin metadata.

Do not add `.lean` files to this directory unless the lib also gets real
submodules; adding stray modules changes the build graph of this lib.
