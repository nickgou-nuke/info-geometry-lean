# Nambu and metriplectic focused verification

## Current status

**Proof candidates; native Lean acceptance has not passed.** Focused CI
[45181377416](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45181377416)
at `383ee52b` passed exact-source checkout, dependency-pin validation, Lean
`4.34.1` installation and locked Mathlib hydration. Its five-owner native build
then reported errors in all five new modules, so warnings-as-errors elaboration
and declaration axiom auditing were not reached.

This revision repairs the reported commutator-name ambiguity, premature matrix
simplification, flow unfolding, scalar proof obligations and owned-source
warnings. The statements and operator carriers are retained; the unused
`DecidableEq` instance is omitted from the final injectivity theorem as requested
by the compiler linter. These repairs still require a successful native rerun.
Earlier local attempts were blocked by the shared build lock; they do not
certify this updated source snapshot.

The subsequent [run 45183619232](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45183619232)
at `cac1fff` built the other four owners successfully and reported no warnings
in the five owned sources. Its remaining three Pauli expansion goals retained
identity-matrix entries. Those entry-expansion lists now explicitly apply
`Matrix.one_apply`. The aggregate gate, fresh warning-as-error checks and axiom
audit still require a successful rerun.

Completed checks are independent mathematical/source review, exact symbolic
matrix identities, a bounded forbidden-construct screen, the maintained staged
proof gate, and Python syntax checking for this runner. These are different
checks and do not imply Lean acceptance.

The root environment and integration gates have not passed. Root dependency
pins, hook code, toolchain and shared-lock implementation are unchanged.

## Focused CI and root integration

`.github/workflows/nambu-metriplectic.yml` runs this same verifier on the exact
PR head commit using an anonymous exact-SHA fetch from this public repository,
with submodule recursion disabled, read-only repository permissions, the pinned
toolchain, and only external dependency artifacts cached. The source repository
and SHA are validated before fetching, and no Git credentials are installed.
It uses the existing locked wrapper for dependency hydration and every build,
elaboration and native declaration audit. It records the checked commit/tree,
source hashes, compiler output and audit result as workflow artifacts.

This job is intended to establish focused native acceptance for the five owners.
Its presence is not evidence of a successful run. Root integration remains a
separate gate. On PR #431 at `c30b02b9`, the reviewed-integration job failed during
recursive checkout because `external_ref/open-math-harness` lacks a `.gitmodules`
URL; the root quality job failed because the `HomotopyHypothesis` package
directory was absent. Neither failure reached elaboration of these new owners.

The first focused run, [45179392271](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45179392271)
at `3561393e`, also stopped before Lean: `actions/checkout` fetched the exact
commit successfully, but its credential cleanup recursively inspected the same
unmapped gitlink even with `submodules: false`. The focused workflow now uses
anonymous Git fetch and detached checkout, without changing `.gitmodules`,
gitlinks, dependency pins, or the native acceptance gate. A minimal Git 2.56.1
fixture reproduced the cleanup failure and confirmed that this checkout method
preserves the exact source revision and a clean tracked tree. A new successful
native run is still required.

The proposed Peirce-defect, Klein-four and KMS-coordinate follow-up remains in
candidate review until the baseline native build, warnings-as-errors checks and
axiom audit complete successfully.

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
