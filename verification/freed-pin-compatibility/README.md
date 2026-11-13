# Focused Pin compatibility verification

This project builds the exact repository owners under `../../lean`. It uses
the root-pinned Lean, Mathlib, and LeanArchitect revisions, with the shared
package directory and the repository's shared build lock. It preserves
the root package, its dependency pins, quality-gate criteria, and root gate
entrypoints.

From the repository root, with the pinned `lake` executable on `PATH`:

```sh
python3 verification/freed-pin-compatibility/check.py exe cache get
python3 verification/freed-pin-compatibility/check.py build
python3 verification/freed-pin-compatibility/check.py env lean \
  -DwarningAsError=true \
  "$PWD/lean/InfoGeometry/Clifford/FreedPinCompatibilityAudit.lean"
```

The default target is
`InfoGeometry.Clifford.FreedPinCompatibilityAudit`. Its imports cover the
representation, graded matrix and Clifford tensor Morita, concrete Klein
differential operators, linear domain transport, Pin and exponential
families, native Fredholm transport, and compact-phase obstruction owners.

The audit checks every declaration owned by those selected mathematical
modules, including private and generated declarations. It uses Lean's native
`collectAxioms`, rejects unsafe and partial declarations, and permits only
`propext`, `Classical.choice`, and `Quot.sound`. Each selected owner must have
at least one audited declaration. The audit body follows the maintained
`tools/quality/reviewed_audit_source.py` generator.

For a specific owner during development:

```sh
python3 verification/freed-pin-compatibility/check.py build \
  InfoGeometry.Clifford.FreedPinRepresentation
```

The source contracts and final validation record belong in
`docs/FREED_PIN_COMPATIBILITY_CONTRACT.md`. A focused build establishes the
selected import closure and its declaration audit. It does not certify
unrelated root default targets, the root optional path dependencies, or
geometric/differential `KO` constructions outside the declared scope.

## Accepted code checkpoint

[CI run 43394851127](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43394851127)
passed the full focused closure and both audit executions at
`8f5bbd0bbc297ce407b184e17eda75510ccba067`. Both executions audited 682
declarations from all 14 selected owners and reported only `propext`,
`Classical.choice`, and `Quot.sound`; the direct audit passed with warnings
treated as errors. Root integration remains blocked by the separately
recorded submodule/path-package failures. See the contract for exact owner
counts, inputs, remaining mathematical edges, and integration evidence.
