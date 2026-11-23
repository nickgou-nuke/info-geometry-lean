# Nambu and metriplectic focused verification

## Current status

**Proof candidates; native Lean acceptance is pending.** The canonical prerequisite
build was started on 2026-11-23 and remains waiting for the shared build lock at
this record. It has not emitted the acquired-lock command or compiler output.
The complete five-owner runner was then queued through the same shared lock;
its status is `toolchain`, waiting before its native version probe can execute.
The new declarations have not yet been kernel-checked or axiom-audited in this task.

Completed checks are independent mathematical/source review, exact symbolic
matrix identities, a bounded forbidden-construct screen, the maintained staged
proof gate, and Python syntax checking for this runner. These are different
checks and do not imply Lean acceptance.

The root environment and publication gates have not passed. Root dependency
pins, hook code, toolchain and shared-lock implementation are unchanged.

## Reproduce

Use the repository's pinned Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency update is needed.

The existing focused package owns the dependency manifest and lock wrapper.
For a fresh checkout, hydrate its pinned dependencies and then run:

```bash
python3 verification/real-matrix-split/check.py exe cache get
python3 verification/nambu-metriplectic/check.py
```

An existing exact-pin cache can be used with Lake's documented package override:

```bash
python3 verification/nambu-metriplectic/check.py --package-root /absolute/path/to/packages
```

The runner checks every focused pin against the root manifest and against the
dependency's actual Git HEAD; it rejects modified or untracked dependency
source/configuration. It also checks the selected Lake version and the actual
`lake env lean --version` against the pinned Lean release before compilation.
The override changes only the local source location,
not the dependency revisions. It introduces no symlinked Lake root.

Every build, source elaboration, and native declaration audit delegates to the unchanged
`verification/real-matrix-split/check.py`, which validates checkout integrity
and acquires `/tmp/info-geometry-build.lock`. Builds remain serialized.

## Coverage

The five selected owners are:

```text
InfoGeometry.Algebra.AssociativeNambuScalarReduction
InfoGeometry.Algebra.RealPauliNambuSign
InfoGeometry.Clifford.Cl11MetriplecticPencil
InfoGeometry.Clifford.Cl11EighthRoot
InfoGeometry.Thermo.MatrixGENERICRealization
```

The runner performs a focused Lake build, then a fresh warnings-as-errors
elaboration of each owner. It generates the maintained native declaration audit,
covering all owned declarations including private/generated names, and permits
only `propext`, `Classical.choice`, and `Quot.sound`. It checks source hashes
before and after the run and records exact commands, versions, pins and counts
in `artifacts/verification/nambu-metriplectic/status.json`.

A `passed` record is written only after every native command and audit completes.
An interrupted or waiting run is not accepted. This focused package does not
certify the root default targets, unrelated dependency configuration, or the
unresolved analytic GRH/Weil/Stokes claims in the original notes.

Source and scope contract: `docs/NAMBU_METRIPLECTIC_CONTRACT.md`.
