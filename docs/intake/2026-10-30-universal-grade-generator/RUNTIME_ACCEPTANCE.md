# Independent runtime acceptance: universal grade generator

**Disposition: ACCEPTED.**

Reviewer: `grade_owner_search` (QA-A), independent of the source authors and
the semantic reviewer. Acceptance timestamp: `2026-10-30T11:01:49.353897+00:00`. No theorem source or
live repository file was authored or modified by QA.

## Exact accepted scope

The accepted surface is the eight new Lean owners and their exact
26-module repository import closure at the unchanged Lean `4.34.1` and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins. It uses full associative rings, real
operator algebras, and the dense full real four-by-four matrix instance.
This receipt makes no claim that the unrelated root package or all global
GitHub workflows pass.

The final semantic review is `SEMANTIC_AUDIT_V2.md` /
`SEMANTIC_AUDIT_V2.json`, with verdict **PASS** and no unresolved semantic
nonconformances. Every reviewed declaration name was reconciled against
the actual native audit output.

## Native verification and the leaf update

1. The maintained `check_universal_grade_generator.py` selector completed a
   full exact-source run: **26 modules**, all eight new targets compiled with
   warnings as errors, **1,287 kernel declarations** audited, and a native
   isolated Lake build completed successfully.
2. The unchanged staged-proof gate then identified a lexical recognition
   issue for the existing multi-argument matrix witnesses. The author added
   `reflection_tripotent_noncommute`, proving that two existing dense
   self-adjoint matrices fail to commute. No gate or screener was weakened.
   The unchanged gate passed on that correction.
3. The corrected matrix leaf was independently strict-compiled, all **44**
   declarations owned by that leaf were audited, and `lake build
   InfoGeometry.Canonical.TripotentMatrixExample` completed successfully in
   the existing isolated native package. All **25 other source hashes**
   matched the original successful full run, and no module in that closure
   depends on the changed leaf.

The final composite total is therefore **1,288 = 1,287 − 43 + 44** audited
declarations, including **143** declarations owned by the eight new modules.
The explicit authored surface contains **93 theorems, 5 definitions, and one
carrier abbreviation**. The additional kernel declarations are generated
proof auxiliaries and equations, also covered by the exhaustive audit.

The full V1 logs and status were preserved byte-for-byte. The original V1
matrix source was preserved before refreshing the isolated verification copy.
This is an explicit full-run-plus-leaf-update acceptance; it is not described
as a fresh run of the full checker at the V2 hash.

| New owner | Explicit theorems | Definitions | Kernel declarations |
|---|---:|---:|---:|
| `Core.IdempotencyDefect` | 12 | 1 | 23 |
| `Core.PeirceDefect` | 12 | 0 | 17 |
| `Core.PeirceDefectAdjoint` | 7 | 0 | 12 |
| `Core.DefectIteration` | 12 | 0 | 12 |
| `Core.TripotentDefect` | 9 | 0 | 18 |
| `Core.TripotentAdjoint` | 7 | 0 | 7 |
| `Core.TripotentEigenspaces` | 10 | 0 | 10 |
| `Canonical.TripotentMatrixExample` | 24 | 4 | 44 |

## Axioms, source integrity, and staged gate

Both native audit phases reported exactly
`[propext, Classical.choice, Quot.sound]`. No custom axiom, proof hole,
unsafe or partial declaration, or `native_decide` was accepted.

Final source reconciliation verified all of the following:

- The working source, stage-0 Git blobs, and isolated package source copies
  agree for all 26 modules.
- All eight final frozen hashes agree with the V2 semantic review.
- Every one of the 93 theorem names, five definition names, and the carrier
  abbreviation appears in its module's native audit output.
- Lean and Mathlib pin files remain equal to the baseline and staged copies.
- Mathlib and all of its pinned transitive dependencies remain clean at their
  expected revisions.
- All maintained verification tools, the OpenGauss screener, and the workflow
  retain their previously recorded source hashes.
- `git diff --check` and `git diff --cached --check` both pass.
- `python3 tools/quality/proof_proxy_staged_gate.py` passes unchanged.

The final matrix source SHA-256 is
`f188c713d38c2c7ad48e32fc0448ddb0ca431395606c1c13bd9feead9aadf195`.
Complete source hashes, exact declaration coverage, dependency edges, pins,
staged-tree fingerprints, and evidence hashes are in
`FINAL_SOURCE_FINGERPRINT.json`. Its SHA-256 is
`9e232ff09f8d2a9c4e3deda8f8c0ed4b8eeb47b6fa246782f781bed50de3063f`.

## Lexical checks and reviewed warnings

The semantic vacuity gate scanned all eight final owners and returned exit
code zero with no errors. Its four advisory short-proof findings are
`defect_zero`, `map_defect`, `defect_mul_eq_zero`, and
`mul_defect_eq_zero`. These are ordinary normalization, ring-hom naturality,
and ordered zero-product consequences. Their complete proofs explicitly
use the actual definitions or hypotheses.

The legacy vacuity linter returned exit code zero on all eight files. Its
`no_hyp_use` groups in the adjoint and matrix files are lexical limitations:
it inspects a header/first proof line and captures combined binders such as
`i j`. The inspected proofs use the individual indices, or establish the
intended definitional native-adjoint bridge. No linter was modified or
suppressed. The exact findings and their disposition are retained in the
companion JSON.

The maintained constructivity scan and the additional comment/string-masked
placeholder, unsafe/partial/native-decision, and structure/class scans
reported **zero findings** across all eight final files. No new theorem
carrier fields hide an assumed conclusion.

All eight new owners produced **zero strict warnings**. The unchanged
imported owners produced 84 warning emissions in the full source check,
principally unused section variables, overlapping instance parameters, and
deprecated APIs:

| Existing owner | Warning emissions |
|---|---:|
| `Physics.Algebra.TripotentPeirceProjectors` | 6 |
| `Physics.TripotentAdjointDerivation` | 4 |
| `OperatorAlgebra.TKKConformalClosure` | 26 |
| `OperatorAlgebra.SuperTKKConformalClosure` | 34 |
| `Singular.MoorePenrose` | 14 |

These inherited diagnostics are recorded, not silently treated as new
source defects or as evidence that the root package passed.

## Commands and retained evidence

The complete run used:

```bash
PATH=/tmp/operator-pr-toolchain/lean-4.34.1-linux/bin:$PATH \
PYTHONDONTWRITEBYTECODE=1 \
python3 tools/quality/check_universal_grade_generator.py \
  --mathlib-root /workspace/scratch/3c7848773029/grade-validation/mathlib \
  --output /workspace/scratch/3c7848773029/grade-validation/final
```

The update used the same shared build lock and pinned compiler, with the
maintained `audit_source([leaf])` generator. Its decisive commands were
strict `lean -DwarningAsError=true -o ... <exact copied leaf>`, native Lean
execution of the generated complete leaf audit, and
`lake build InfoGeometry.Canonical.TripotentMatrixExample` in the existing
isolated package. Full argument arrays, locations, and exit statuses are
retained in `RUNTIME_ACCEPTANCE.json` and the delta status record.

The initial delta harness invocation stopped at import resolution because
its leading repository artifact root was incomplete. A fresh retry used
regular, byte-checked copies of the accepted dependency artifacts. No Lean
source, gate, or dependency manifest was changed to resolve that harness
issue. The failed attempt remains recorded separately.

Full logs remain in `grade-validation/final` and
`grade-validation/final-v2-retry`; the failed harness attempt remains in
`grade-validation/final-v2`. Only this receipt, its companion JSON, and the
final fingerprint need promotion as curated acceptance records.

**Residual open debt for this scoped mathematical artifact: none.**
Any accepted Lean source hash change requires renewed affected-source
verification and semantic review.
