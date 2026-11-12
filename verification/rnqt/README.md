# Focused real-number quantum theory verification

Run from the repository root with its pinned Lean toolchain available:

```bash
python3 verification/rnqt/check.py build
```

The default target is `InfoGeometry.Quantum.RealificationAudit`. This focused
project compiles the canonical repository sources imported by that audit.
The audit source specifies the exact declarations and semantic claims checked.

The wrapper acquires the maintained shared build lock and rejects linked Git
worktrees and symlinked Lake roots. The package uses the ordinary repository
dependency cache and retains the root pins: Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The manifest pins the full Mathlib
dependency closure. The root Lake configuration, manifest, and toolchain are
unchanged.

A successful focused build certifies only the selected sources and their
imports. It does not certify optional root path dependencies, all root default
targets, or the repository pre-push gate.

For an explicit target or a fresh audit elaboration:

```bash
python3 verification/rnqt/check.py build InfoGeometry.Quantum.RealificationAudit
python3 verification/rnqt/check.py env lean lean/InfoGeometry/Quantum/RealificationAudit.lean
```
