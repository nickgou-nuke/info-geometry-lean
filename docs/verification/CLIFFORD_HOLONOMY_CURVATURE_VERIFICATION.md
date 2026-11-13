# Clifford, BCH, holonomy, and curvature verification

## Result and scope

The focused native verification **passed** at source checkpoint
`3a584a2859ebe5854f1c0f906cfb917c9c548249`, based on main revision
`a392af178af1fe2bcba2ba39eb405700c6ee103c`. The source checkpoint tree is
`f46de76cadbe04ff8f6ddb318969a65790cc78a6`.

The root-workspace build and actual pre-push hook **failed** because the
configured path package `external_refs/homotopy-hypothesis-lean4` is absent.
This record supports a draft for review and preservation; it does not certify
the canonical aggregate, the full repository, or publication-gate acceptance.
Remote workflow results are recorded separately in the pull request after
they are observed.

The seven new owners contain **94 named theorems** and **206 declarations**
enumerated by Lean's native environment, including definitions and generated
support declarations. The audit additionally covers **109 declarations** in
four existing owners whose imports were narrowed. All coefficient rings retain
their noncommutative scope. The mathematical contract and corrected dependency
diagram are in [the contract](../CLIFFORD_HOLONOMY_CURVATURE_CONTRACT.md).

## Fresh independent verification

| Check | Observed result |
| --- | --- |
| Exact repository source closure | 22 modules freshly compiled; no incremental artifact reuse |
| Selected owners | All 11 compiled with zero warnings |
| Native declaration audit | 315 declarations; only `propext`, `Classical.choice`, and `Quot.sound` |
| Strict placeholder scans | All 11 commands exited 0; 0 hard, 11 soft findings |
| Strict semantic scan at warning threshold | Exit 1; 22 reviewed warnings, 0 errors |
| Raw banned-proof-token scan | No matches in the 11 selected owners |
| Imported compiler warnings | 9 warnings in three unchanged base-revision owners |
| Actual source pre-commit hook | Passed when committing the source checkpoint |
| Maintained root Lake wrapper | Exit 1 during dependency initialization |
| Actual new-ref pre-push hook | Exit 1; build failed, subsequent static checks passed |

Lean is `leanprover/lean4:v4.34.1`. Mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Builds used the shared
`/tmp/info-geometry-build.lock`. The independent reviewer did not author or
modify these sources and ran the checker afresh, without the incremental or
audit-skipping options.

The complete reviewer report contains the per-owner declaration counts,
individual dispositions of all 22 semantic warnings and 11 soft placeholder
findings, imported-warning provenance, old-owner body comparisons, and
mathematical scope review:
[independent acceptance](clifford-holonomy-curvature/independent-acceptance.md).

The nine imported warnings are one deprecated import in `SplitQ11`, six unused
simp arguments in `SplitAtomDoubling`, and two unused section-variable
assumptions in `AssociativeGaugeConnection`. Those three source files match the
base byte for byte. The warnings were recorded rather than suppressed.

The pinned dependency cache was used for native Mathlib imports; the repository
closure itself was rebuilt from copied source. This is not a source rebuild of
every dependency package. A pre-existing documentation-only modification in
the pinned nested Batteries checkout was inspected and preserved; no Batteries
Lean-source change was observed.

## Reproduction

From the repository root, the successful native command was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/66380c6bf432/info-geometry-lean/.lake/packages/mathlib \
  --lean /workspace/scratch/4796737fb777/lean-environment/lean-4.34.1-linux/bin/lean \
  --target InfoGeometry.Algebra.StrictUpper3 \
  --target InfoGeometry.Algebra.StrictUpperBCH3 \
  --target InfoGeometry.Algebra.QuaternionCayleyPair \
  --target InfoGeometry.Clifford.SplitAtomQuaternion \
  --target InfoGeometry.Geometry.AssociativeBianchi \
  --target InfoGeometry.OperatorAlgebra.WeightedPermutationHolonomy \
  --target InfoGeometry.Canonical.CliffordHolonomyCurvature \
  --target InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR \
  --target InfoGeometry.OperatorAlgebra.ThreeZ2OperatorGradings \
  --target InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity \
  --target InfoGeometry.OperatorAlgebra.InnerConjugation \
  --output /workspace/scratch/d18a558d1d7d/chain-qa-final
```

The absolute executable and Mathlib locations above describe the observed
local run; another machine must supply its own paths at the same pins. The
dedicated workflow fetches those exact pins and invokes the same maintained
checker. It explicitly checks zero warnings for all eleven selected owners.
Its semantic scan fails on errors and preserves warnings. The independent
local review additionally used `--fail-on warning`, whose nonzero result is
reported rather than converted into a pass.

The strict static commands, raw outputs, helper hashes, and source comparisons
are in [static-gates.json](clifford-holonomy-curvature/static-gates.json).

## Root integration and publication gate

The actual maintained root invocation was:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.CliffordHolonomyCurvature
```

It exited 1 with:

```text
error: HomotopyHypothesis: package directory not found:
.../external_refs/homotopy-hypothesis-lean4
```

The actual `.githooks/pre-push` was then invoked for a new remote ref at the
source checkpoint, using the verified main revision as its comparison base.
Its exact arguments and stdin are preserved with its exit status. The hook's
incremental build selected all twelve changed Lean files, including
`InfoGeometry.Canonical.All`, and encountered the same dependency error.
Its axiom/debt text scan, semantic-content audit, tracked-scope audit, and
quarantined-artifact audit completed successfully. The overall hook exited 1.
The hook's later internal step advertised as a full gate was not reached.

This failure occurs before the root workspace can elaborate the selected
targets; it does not contradict the independently successful pinned source
closure check. It also cannot be treated as successful root integration.
No dependency pin, gate implementation, or gate threshold was changed to
remove the failure. Initializing or repairing unrelated external packages is
outside this mathematical change. Draft preservation under the user's
standing publication instruction does not imply merge readiness.

## Durable evidence

| File | Contents |
| --- | --- |
| [source-closure.json](clifford-holonomy-curvature/source-closure.json) | Exact sources, import graph, compiler results, declaration counts, source and verifier hashes |
| [axiom-audit.txt](clifford-holonomy-curvature/axiom-audit.txt) | Native axiom dependencies for all 315 audited declarations |
| [native-logs.json](clifford-holonomy-curvature/native-logs.json) | All module compiler logs, generated native audit source, environment record, and original evidence manifest |
| [placeholder-findings.json](clifford-holonomy-curvature/placeholder-findings.json) | All eleven strict placeholder reports |
| [semantic-findings.json](clifford-holonomy-curvature/semantic-findings.json) | Complete strict semantic findings |
| [root-build.json](clifford-holonomy-curvature/root-build.json), [root-build.txt](clifford-holonomy-curvature/root-build.txt) | Maintained root wrapper command, status, and raw log |
| [source-pre-push.json](clifford-holonomy-curvature/source-pre-push.json), [source-pre-push.txt](clifford-holonomy-curvature/source-pre-push.txt) | Completed source-checkpoint hook invocation, exit status, and raw log |
| [evidence-sha256.json](clifford-holonomy-curvature/evidence-sha256.json) | Hashes of the preserved evidence files and this report |

A documentation-only evidence commit follows the tested source checkpoint.
All 22 repository-source fingerprints and all four maintained native-verifier
fingerprints were reconciled before recording this evidence. Native acceptance
is tied to these exact source hashes. Registering the entry point in
`Canonical.All` does not certify that aggregate or downstream consumers outside
the checked closure. No full-default-target, every-tracked-file, analytic,
categorical-braiding, or arbitrary-ring Clifford-classification claim is made.
