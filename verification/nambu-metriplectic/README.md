# Nambu and metriplectic focused verification

## Acceptance by source revision

The **five-owner baseline passed** at `d7c16f1605aa9877e92ac2c515d1a70460cd3b3e`
in [run 45185104156](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45185104156).
All five builds, fresh `-DwarningAsError=true` elaborations and the complete
owned-declaration audit passed. The audit covered **157 declarations**, including
private/generated names, and reported only `propext`, `Classical.choice` and
`Quot.sound`. Its [uploaded evidence](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45185104156/artifacts/14824355326)
records the exact source revision, versions, pins and commands.

Only after that result were `Cl11MetriplecticSymmetry` and
`MetriplecticZetaKMSBridge` integrated. The verifier now checks **all seven
owners together**. Acceptance of this expanded scope requires a successful
result for the checked source revision; the five-owner result does not certify
the additions. Consult the exact head's [PR checks](https://github.com/nickgou-nuke/info-geometry-lean/pull/431/checks)
and uploaded `status.json`, rather than inferring acceptance from workflow
presence or from a successful earlier revision.

Independent source review, symbolic identities, the maintained staged proof
integrity gate and syntax/whitespace checks are separate evidence. They do not
replace the native gate. Local attempts blocked by the shared build lock do
not certify a later source snapshot.

## Focused CI and root integration

`.github/workflows/nambu-metriplectic.yml` runs this verifier on the exact PR
head using an anonymous exact-SHA fetch from this public repository. Repository
and SHA inputs are validated, submodule recursion is disabled, and no Git
credentials are installed. Permissions remain read-only. Only the pinned
toolchain and external dependency artifacts are cached; repository source
build artifacts are fresh.

Dependency hydration, compilation, fresh elaboration and native axiom auditing
use the unchanged canonical shared-lock wrapper. The workflow records the
checked commit/tree, source hashes, compiler output and audit result, and checks
that owned sources and pinned configuration did not change during validation.

| Focused run | Observed result |
| --- | --- |
| [45179392271](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45179392271), `3561393e` | Checkout-action credential cleanup traversed an unmapped gitlink and failed before Lean. Anonymous exact-SHA checkout repairs this without changing gitlinks or `.gitmodules`. |
| [45181377416](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45181377416), `383ee52b` | Native build exposed baseline proof and linter errors in all five owners. |
| [45183619232](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45183619232), `cac1fff` | Four owners built; three Pauli expansion goals required explicit identity-entry normalization. No owned-source warnings were reported. |
| [45185104156](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45185104156), `d7c16f16` | Full five-owner native acceptance: 157 declarations audited. |
| [45186628451](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45186628451), `ff6e24df` | The new Klein-four import closure required `InfoGeometryCore.Basic`, which the focused package had not exposed. The original five owners built successfully; the expanded gate did not pass. |

The focused package now exposes the existing tracked source at
`lib/InfoGeometryCore` as an additional native Lean library. This is the same
plain library already required by the root package, using the same pinned
Mathlib revision. Its source is included in CI triggers and the post-build
tracked-source check. No external dependency or manifest revision is added;
the seven-owner native result must still validate the expanded import closure.

**Root integration remains separate and is not certified.** At the original
PR head `c30b02b9`, Reviewed PR Integration failed during recursive checkout
because `external_ref/open-math-harness` lacks a `.gitmodules` URL. The root
quality job failed because the `HomotopyHypothesis` package directory was
absent. Focused native acceptance does not clear these root gates. Dependency
pins, root manifests, hook code and the shared-lock implementation are unchanged.

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

The seven selected owners are:

```text
InfoGeometry.Algebra.AssociativeNambuScalarReduction
InfoGeometry.Algebra.RealPauliNambuSign
InfoGeometry.Clifford.Cl11MetriplecticPencil
InfoGeometry.Clifford.Cl11EighthRoot
InfoGeometry.Thermo.MatrixGENERICRealization
InfoGeometry.Clifford.Cl11MetriplecticSymmetry
InfoGeometry.NCG.MetriplecticZetaKMSBridge
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
