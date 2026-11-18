# Radon diffusion–decay validation record

Date: 2026-11-18. This record identifies the exact checked source, its scope,
and the limits of its repository-integration coverage.

## Native verification

- Base repository commit: `08c34e03f610b452e03422037949196dc7d92d6d`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib commit: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The repository toolchain and dependency manifests are unchanged.
- All nine mathematical owners below, the focused umbrella, and the axiom
  audit compiled successfully. The checked snapshots match the integrated files
  byte-for-byte by SHA-256.
- The eight new owners expose 174 public definitions and theorems. The existing
  integral owner adds 16 reused declarations to the explicit audit surface.

The checks ran in an independent checkout of the exact pinned Mathlib commit,
with official Lean 4.34.1 and its matching Mathlib cache. Task sources were copied
under `InfoGeometry/Nuclear/`, and their compiled objects were placed under that
checkout's `.lake/build/lib/lean/InfoGeometry/Nuclear/`. Each downstream owner
therefore imported the compiled task dependencies from the same verification
environment. This is focused native verification, not a root-project build.

Compilation used the repository's maintained workspace-integrity validator,
shared build lock, and `build_lean_command` routing. The final owner/audit batch
and the preceding owner checks were serialized by that lock. The resulting
native command for each owner was:

```text
<pinned-lake> env lean InfoGeometry/Nuclear/<Owner>.lean \
  -o <pinned-mathlib>/.lake/build/lib/lean/InfoGeometry/Nuclear/<Owner>.olean
```

`tools/infra/run_locked_lean.py` SHA-256:
`e7280cb69266158a8a062d43c5ed6a9d4dee4bb9275c6c796dfd1d8fdde7a9b0`.
No lock was removed, replaced, or bypassed, and no other task's build was stopped.

| Source under `lean/InfoGeometry/Nuclear/` | Native result | SHA-256 |
|---|---|---|
| `DetectorBeerLambert.lean` | PASS | `72901948f3ecd8895b9d2cba7f5ad8757371e791948f985b6d15da8a95696a37` |
| `RadonDiffusionProfiles.lean` | PASS | `dbde727b981ab0552fd9f50189a8efb0b7d532f684e342795c3dc490acb01991` |
| `RadonDataAudit.lean` | PASS | `97e1b6bcc7175507e8281fc4be587d3fe24fd65a6126719368a53e2723883699` |
| `DiffusionTransfer.lean` | PASS | `fb2dc2e3a794c9ccb8de14042c3a900cef2332d1abd025655fe114cbff579486` |
| `DiffusionTransferODE.lean` | PASS | `aa49727cce45c2ff55c0f7ea2fec88826122870f30071861874c8c4ec1a5cb89` |
| `DiffusionParameters.lean` | PASS | `20ae3e9a4602eedf7dc3c43bf6d853e8494ac138a9e23e2958eac68fc3c63cf2` |
| `DecayAcquisitionCorrection.lean` | PASS | `16dbf78d7938bd196fc22568b9c42855a98ee3d2bf5fde078d0a5ad6aef4ad25` |
| `RadonBoundaryModels.lean` | PASS | `b99d19687541f72378aea5503bbcd0cb4e5f0a6fa3fd68ed2edb049c00d75851` |
| `RadonObservationArtifacts.lean` | PASS | `25a2b026df3bb108cbaf1a0e37fcab45c01ea8a50585099a4d229e48893d787a` |
| `RadonDiffusion.lean` | PASS | `422fcf32778b7e6a4117b5af758e078e437cc5b9948c1db2223a6fd62ddb4fa1` |
| `RadonDiffusionAxiomAudit.lean` | PASS | `656977e2801012f8ca2a4584a0eb6b8c71c62bf64e0221740bedeab4e37d6604` |

## Transitive axiom audit

`RadonDiffusionAxiomAudit.lean` prints all 190 public declaration reports,
then inspects every declaration in the task namespaces, including private and
generated helpers and the reused integral namespace. It calls Lean's
`collectAxioms` transitively and raises an error if any dependency is outside
`propext`, `Classical.choice`, and `Quot.sound`.

Actual successful audit summary:

```text
AUDIT_TOTAL 325 declarations; AXIOM_UNION [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, authored axioms, `sorry`, `admit`, or `native_decide` is used by the
new mathematical source. The source proof gate and independent semantic review
are additional checks; they do not replace the native result above.

## Repository integration

The focused verification above does not certify the root Lake package or the
repository pre-push gate. The actual gate is assessed separately against the
completed local commit, and its result accompanies that proposed commit.

Read-only setup inspection found absent root path packages
`external_refs/homotopy-hypothesis-lean4` and `external_refs/atlas-lean`.
The current Lake files and manifest do not supply complete immutable source
provenance for either path. Historical Atlas inventory entries are leads, not
a replacement dependency specification. The configured GIFT submodule is also
uninitialized; unlike those two packages, it has a recorded URL and gitlink
revision. The tracked `InfoGeometryCore` source is present. No external package
was replaced by a guessed revision, and no dependency pin or toolchain was
changed to manufacture a root-build result.

The focused production import is `InfoGeometry.Nuclear.RadonDiffusion`, exposed
through `InfoGeometry.Nuclear.All`. The diagnostic axiom-audit module is kept out
of the production umbrella. Independent read-only review found no import cycle.
The existing Beer–Lambert owner's definitions, statements, and proof bodies are
unchanged; only its imports and required file header changed. The bounded
consumer review does not certify the full repository's transitive imports.

## Numerical reproduction and semantic review

The numerical audit was reproduced from the preserved intake using:

```bash
python3 scripts/analysis/audit_radon_diffusion.py \
  data/radon_diffusion/intake_20261118.txt /tmp/radon-audit
```

The execution environment used Python 3.12.14, NumPy 2.3.5, and SciPy 1.17.0.
Audit-script SHA-256: `b63e56fbda345ad40f655972663842174a81c9ba283b7265442f8afe57b36364`.
Intake SHA-256:
`882b6799b2787041c86e07b36c7fe892ee1e7807756e05273227ac73b9411754`.
Output CSV files use LF line endings. Authored Lean, Python, and documentation
passed `git diff --check`; preserved source intakes retain their original bytes,
including any original whitespace.

An additional 50-digit Decimal calculation reproduced all 18 corrected rates
to within `5.69e-14` counts/s and all 18 fixed-model R-squared values to within
`4.45e-16`. A separate formula-reference check confirmed that all 125 repairs
shift only relative row references by one; the 304 parsed references preserve
absolute coordinates and all constants/operators. This additional arithmetic
cross-check was performed by the numerical script's author; it is not claimed
as an independent-author audit.

Independent read-only reviews covered the physical contracts, operator order,
actual derivatives and integrals, numerical conclusions, and import integration.
Their wording corrections were incorporated. These reviews did not run a second
compiler. Exact rational Lean certificates concern the entered data; floating
point regressions remain reproducible descriptive calculations.

No experimental steady state, secular equilibrium, adsorption saturation,
detector calibration, fitted confidence interval, or physical outlet selection
is certified by these checks. See `RADON_DIFFUSION_DECAY_CONTRACT.md` for the
assumptions and corrected model interpretation. The subsequent leakage audit is
documented in `RADON_LEAKAGE_MODEL_AUDIT.md`, with reproducible numerical outputs
under `data/radon_diffusion/leakage/`. Its source hashes, fixed formulas, model
interpretations, and conditional fit results received an additional independent
read-only review. The new two-reservoir/Robin and observation-artifact owners are
included in the same exact-source and transitive-axiom checks listed above.
