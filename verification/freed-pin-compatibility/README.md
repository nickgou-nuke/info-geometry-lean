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
differential operators and smooth Morita realization, actual Pin frame
families and their joint operator/corner comparisons, linear domain transport,
analytic suspension compatibility, native Fredholm transport, and compact-phase
obstruction owners.

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

## Accepted concrete checkpoint

[CI run 43469884874](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43469884874)
passed the complete focused closure (9059 build jobs) at
`bc3cea7eebc70360085200126ebb3fca101508e2`. Both exhaustive audit executions
checked **973 distinct declarations across all 18 selected owners**, with
matching ordered declaration names and owner counts. Both reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; the direct audit passed with
`-DwarningAsError=true`.

The four new concrete owners contribute 291 declarations: smooth Morita (89),
Pin frame family (120), joint Morita/frame comparison (49), and analytic
suspension compatibility (33). The earlier fourteen owner counts are
unchanged. Two nonfatal unused-simplifier-argument lints occur in the joint
owner during its ordinary build; no proof errors remain.

Root integration remains blocked by the separately recorded checkout and
path-package failures. This acceptance covers the concrete smooth-domain
construction and the conditional analytic compatibility theorems; it does not
construct the Klein Hilbert/Sobolev Fredholm seed, an action of the canonical
infinite Clifford tail on its concrete coefficient module, or a differential
`KO` pushforward. See the contract for exact source trees, owner counts,
artifact links, mathematical boundaries, and integration evidence.

## Earlier accepted base

[CI run 43394851127](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43394851127)
passed the full focused closure and both audit executions at
`8f5bbd0bbc297ce407b184e17eda75510ccba067`. Both executions audited 682
declarations from all 14 selected owners and reported only `propext`,
`Classical.choice`, and `Quot.sound`; the direct audit passed with warnings
treated as errors. Root integration remains blocked by the separately
recorded submodule/path-package failures. See the contract for exact owner
counts, inputs, remaining mathematical edges, and integration evidence.
