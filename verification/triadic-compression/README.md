# Focused verification of tripotent compression

This project checks the canonical sources in `../../lean`, with the exact
root Lean and Mathlib revisions. It shares ordinary dependency directories
inside this independent checkout; no Lake directory is symlinked. Its own
build products remain under this verification project's `.lake/build`.

From the repository root, with Lean `v4.34.1` on `PATH`:

```bash
python3 verification/triadic-compression/check.py build
python3 verification/triadic-compression/check.py env lean \
  "$PWD/lean/InfoGeometry/Core/TripotentCompressionAudit.lean"
```

`check.py` uses the existing workspace-integrity check and global build lock.
The audit enumerates all declarations owned by the selected nine modules,
checks transitive axiom dependencies against `propext`, `Classical.choice`,
and `Quot.sound`, and rejects newly introduced axioms or unsafe declarations.
It also emits direct dependencies between the audited owner declarations.
This makes the mathematical dependency graph inspectable from Lean terms.

The focused build does not certify the root's unrelated path dependencies,
all default targets, or its publication gate. Root integration status and
independent acceptance are reported separately in `RESULTS.md`.

The exact mathematical scope and rejected implications are recorded in
[`TRIADIC_COMPRESSION_CONTRACT.md`](../../docs/TRIADIC_COMPRESSION_CONTRACT.md).
