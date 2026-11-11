# Twistor invariants and native Hadamard verification

This focused package checks the changed twistor owners and the native matrix
Hadamard bridge, followed by a fresh axiom audit. It uses the parent repository's
Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins.
It does not require the unrelated root package's optional path dependencies.

Run from the repository root:

```bash
python3 verification/twistor-hadamard/check.py build
python3 verification/twistor-hadamard/check.py env lean "$PWD/lean/InfoGeometry/Canonical/TwistorHadamardAudit.lean"
```

The wrapper uses the repository's shared build lock and rejects linked
worktrees or symlinked Lake roots. The package reads the canonical `lean/`
source and writes its own focused build artifacts. Its dependency cache is
the ordinary parent `.lake/packages` directory. Do not change pins, run
`lake update`, or remove caches to repair a build.

The audit prints axiom dependencies for all fourteen new public mathematical
declarations and the reused generic matrix-unit noncommutativity theorem, and checks the exact existing mass/infinity identity and a
conditional fourfold-count induction. The count example does not establish a
recurrence for a geometric object absent from the source.

See [the contract](../../docs/TWISTOR_INVARIANTS_HADAMARD_CONTRACT.md) for
mathematical scope, countermodels, interpretation boundaries, and actual
validation results. Focused success is not a whole-repository certificate or
an exemption from the publication gate.
