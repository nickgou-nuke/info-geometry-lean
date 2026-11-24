# Focused verification: summable compatible functionals

This profile checks the single canonical owner
[`InfoGeometry.Canonical.SummableCompatibleFunctionals`](../../lean/InfoGeometry/Canonical/SummableCompatibleFunctionals.lean).
It covers real pointwise limits from summable compatibility defects, their
explicit tail bound, and normalized native real `PositiveLinearMap` limits
with exact successor and finite pullback compatibility.

The [contract](../../docs/SUMMABLE_COMPATIBLE_FUNCTIONALS_CONTRACT.md) records
the exact hypotheses, proof dependencies, real/complex state boundary, and
corrections and existing-owner reuse for the Gaussian part of the intake.
The unchanged [raw intake](intake-20261124.txt) has SHA256:

```text
9bc02582c6f750ed96e115afc764ecbf9bab2c80bd9f6f3ca6feb1571e6ffb55
```

## Prerequisites

Run from the repository root in an independent checkout. The maintained
workspace checks reject linked Git worktrees and symlinked Lake roots. Keep
the pinned Lean `v4.34.1` runtime on `PATH`, and provide all exact Git
dependencies from the maintained focused manifest. Its Mathlib revision is
`d13f23b723b8a846827a245b89c10fc7d3f11612`, matching the root manifest.

On a fresh checkout, the maintained dependency/cache entrypoint is:

```bash
python3 verification/real-matrix-split/check.py exe cache get
```

The focused runner defaults to `.lake/packages`. Use
`--package-root /absolute/path/to/packages` to select an already provisioned
directory of the same pinned packages. It checks exact dependency revisions,
tracked changes, and nonignored untracked Lean/configuration files before and
after the run. This is the stated Git/source check, not an assertion that
every possible source-shadowing mechanism is detected.

## Build, audit, and final phases

Choose an isolated work directory outside the source repository. A new one
must be empty; an existing one must carry this runner's marker for the same
source checkout. The default is `../summable-compatible-build`. Reuse that
directory for incremental work; the runner preserves existing caches.

For compilation during editing:

```bash
python3 verification/summable-compatible-functionals/check.py --phase build
```

For compilation followed by a fresh native declaration axiom audit:

```bash
python3 verification/summable-compatible-functionals/check.py --phase audit
```

For the final focused result, including fresh owner elaboration with warnings
as errors and a fresh axiom audit:

```bash
python3 verification/summable-compatible-functionals/check.py --phase final
```

`final` includes the preceding checks; running all three phases is unnecessary
for a single final result. The successful receipt statuses are respectively
`build_passed`, `audit_passed`, and `focused_passed`. `final` is also the default
phase. Use `--work /absolute/path/to/isolated-build` to choose another work
directory and `--no-wait` to fail immediately if the shared build lock is held.
There is no arbitrary module-selection option: this profile fixes the owner
above.

## What the runner records and checks

`check.py` holds the repository's maintained shared build lock across the
compiler transaction. It copies the canonical repository import closure into
the isolated Lake project, preserves dependency pins, and verifies source and
control hashes before and after execution. It checks Lean/Lake versions,
resolved executable locations in the same installation, and executable SHA256
fingerprints, then rechecks that runtime identity at the end.

The generated `OwnedDeclarationsAudit.lean` enumerates declarations owned by
the selected module using native Lean environment metadata. It rejects unsafe
or partial declarations and transitive axiom dependencies outside `propext`,
`Classical.choice`, and `Quot.sound`. Native completion markers and declaration
counts are reconciled; the generated audit source is hashed before execution
and checked afterward. The audit result is evidence about these declarations,
not a proof of a stronger mathematical or physical interpretation.

The selected work directory contains:

| Artifact | Meaning |
| --- | --- |
| `status.json` | Latest run status, phase, repository revision, source/control/project hashes, dependency pins, runtime identity, command results, and available axiom counts |
| `logs/run-*/` | Per-run compiler logs and generated audit source |
| `src/` | Exact copied repository sources used by the focused project |

Successful receipts explicitly retain `root_package_build_verified: false`,
`publication_gate_verified: false`, and
`independent_semantic_review_verified_by_this_runner: false`. Those checks
remain distinct. Generated project/cache/log files belong outside the source
checkout.

The [workflow](../../.github/workflows/summable-compatible-functionals.yml)
runs `--phase final`, separately applies the strict changed-mathematics
screener, and uploads compiler and axiom evidence. Local strict screening can
be reproduced with:

```bash
python3 tools/infra/opengauss_screener.py --strict lean/InfoGeometry/Canonical/SummableCompatibleFunctionals.lean
```

## Observed validation status

At documentation preparation on 2026-11-24:

| Surface | Observed result |
| --- | --- |
| Independent mathematical/source review | PASS |
| Strict staged proof gate | PASS |
| Native focused build | Pending |
| Fresh owner elaboration and declaration axiom audit | Pending |

Update this record from the final exact-source receipt before publication.
The stated scope is real pointwise and positive-linear compatibility; no
complex C-star state, GNS/KMS construction, colimit completion, or whole-root
build is certified by this profile.
