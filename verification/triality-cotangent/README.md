# Triality and cotangent action groupoid verification

This isolated Lake package reads canonical owners from `../../lean`. It
preserves the root Lean toolchain and all nine pinned Mathlib dependency
revisions. No proof sources are copied into the verification package.

The mathematical contracts, corrections and source map are in
[`TRIALITY_COTANGENT_CONTRACT_20261124.md`](../../docs/TRIALITY_COTANGENT_CONTRACT_20261124.md).
The seven focused owners cover the native action groupoid, Lie algebra fiber
form, finite invariant dual equivalence, a shear counterexample, exact Cartan
coordinates, faithful native `S₃` action, and the vector-group specialization.

## Commands

From an independent checkout with the pinned Lean release installed:

```bash
set -euo pipefail
python3 verification/triality-cotangent/audit.py
python3 verification/triality-cotangent/check.py exe cache get
python3 verification/triality-cotangent/check.py build
python3 verification/triality-cotangent/check.py env lean lean/InfoGeometry/Geometry/TrialityCotangentAudit.lean > triality-cotangent-axioms.log
python3 verification/triality-cotangent/audit.py --log triality-cotangent-axioms.log
python3 verification/triality-cotangent/check.py build InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
```

`audit.py` enumerates explicit public definitions, theorems, abbreviations and
named instances, following each owner's explicit namespace/section structure.
Compiler-generated recursors/projections are not a separate inventory. The
log checker requires every listed declaration exactly once and permits only
`propext`, `Classical.choice` and `Quot.sound`. A parsed log alone is not
evidence of a successful Lean exit; the workflow requires that exit first.

`check.py` reuses the maintained repository build lock. It verifies the root
and focused pins, exact runtime version and revision consistency, the clean
pinned dependency checkouts, and a before/after hash of the source import
closure and validation controls. It rejects linked worktrees, symlinked Lake
roots and unrecorded overrides. Normal generated dependency artifacts remain
writable. Existing exact checkouts can be selected explicitly with
`--dependency-root /absolute/path/to/packages`; `--lake` selects an installed
runtime and `--no-wait` reports a busy lock without waiting.

The CI workflow compiles the focused owners, runs a fresh declaration/axiom
check, screens the mathematical owners, and separately rebuilds the existing
Cartan consumer after its exact block extraction. The logs are preserved in
one workflow artifact. Whole-repository prerequisite failures, if present,
remain separate from this package's results.
