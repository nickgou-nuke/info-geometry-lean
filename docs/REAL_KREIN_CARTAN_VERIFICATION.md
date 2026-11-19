# Real Krein–Cartan verification record

## Status at initial publication

This is the pre-publication record for the draft PR. Source and independent
review checks have passed. **Native compilation and the declaration axiom
audit are pending; no kernel-verification claim is made at this checkpoint.**
The PR checks and its latest description record the subsequent exact-head
CI result. A successful source scan is not a Lean proof.

The source starts from `08c34e03f610b452e03422037949196dc7d92d6d`, with unchanged
Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## First native run and source repair

The first exact-head workflow,
[44052828391](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44052828391),
reached native compilation at commit
`e2d21dce41f45d56c672ad03f9487b608664cd2e` and failed. Toolchain setup and cache
hydration succeeded. `RealMetricAdjoint` needed explicit matrix coercions on
both factors of the square-one hypotheses. `RealKreinTrace` lacked the native
`StarOrderedRing ℝ` instance import. The two files also reported thirteen
warnings. `WeightedAdjointCompatibility` and `RealKreinDensityCounterexample`
compiled with zero warnings; `RealMetricTransport` was blocked by its dependency.
The native declaration audit was not reached.

The source repair supplies the explicit coercions, imports the actual instance
owner `Mathlib.Algebra.Order.Star.Real`, and addresses the reported unused
simplifications and section assumptions. It preserves the real matrix carriers
and theorem conclusions. Both repaired files received independent source/API
review. No dependency pin, checker, build lock, linter setting, or CI acceptance
gate was changed. A fresh exact-head run is required before native acceptance.

The failed artifact was downloaded and matched GitHub's recorded SHA256:
`4e75a6ee16ee62c4118a3bf9b906b16228523feddf9de6c726f44c656f911e40`.
Its source snapshots match the exact failed commit.

## Second native run and transport repair

The repaired-head workflow,
[44088345670](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44088345670),
compiled eleven of the twelve repository modules at commit
`a5517c171f23b6144e40bd0c9cfd243bd7fa4708`. Four of the five selected owners
compiled. `RealMetricAdjoint` passed with zero warnings, confirming the first
repair. `RealKreinTrace` compiled and reported two unused `DecidableEq` section
instances. `WeightedAdjointCompatibility` and `RealKreinDensityCounterexample`
again compiled with zero warnings.

The previously blocked `RealMetricTransport` module then exposed an ambiguous
`mul_inv_rev`, unit-inverse coercion/cancellation mismatches, and simplification
of the two ordered inverse witnesses to `True` instead of the required matrix
equalities. This run failed before the native declaration audit. Its success
on individual modules is not acceptance of the complete selected scope.

The second source repair explicitly coerces the inverse unit as `↑(g⁻¹)` and
`↑(w⁻¹)`, qualifies the group theorem `_root_.mul_inv_rev`, and uses the native
`Units.inv_mul` cancellation. The ordered inverse bridge restricts
simplification to the weighted-adjoint definition and unit value/star
coercions, retaining the full noncommutative products. The two reported unused
instances and the resulting unused instance in their positivity helper are
omitted. No theorem is replaced by a weaker conclusion, and no checker,
dependency pin, lock, linter, or acceptance rule is changed. A fresh exact-head
native run is required for this repair.

The downloaded failed artifact matches GitHub's recorded SHA256:
`3a76aff28246f433f5e8dc5d156f177e464a06af2ff7370e36eafc3ff600637c`.
All twelve source snapshots match the failed commit. The artifact manifest's
`checker.log` digest covers its first 3,760 bytes; the final uploaded log is
5,288 bytes because the failure traceback was appended after the digest was
recorded. The remaining manifest entries match their complete files.

## Selected owners

| Module under `InfoGeometry` | Added explicit theorems | Added definitions |
|---|---:|---:|
| `OperatorAlgebra.WeightedAdjointCompatibility` | 2 | 0 |
| `OperatorAlgebra.RealMetricAdjoint` | 3 | 0 |
| `OperatorAlgebra.RealKreinTrace` | 40 | 6 |
| `OperatorAlgebra.RealMetricTransport` | 4 | 0 |
| `Examples.RealKreinDensityCounterexample` | 8 | 2 |
| **Total** | **57** | **8** |

The maintained lexical closure helper selects twelve repository modules for
these five targets. This selection is checked by the native compiler; the
lexical inventory alone is not proof of import resolution. The existing
`RealMatrixSplitAudit.lean` command inventory is regenerated with the five
new declarations in its two already-selected owners. That command-only file
is not one of the five mathematical owners audited by the new workflow.

## Completed checks

| Check | Observed result and scope |
|---|---|
| `placeholder_audit.py --root <owner> --strict` for all five owners | Exit 0 for each. No forbidden proof placeholder detected. |
| `semantic_vacuity_gate.py <five owners> --fail-on error` | Exit 0; thirteen `trivial_surface` warnings reviewed. Eight concern new parity/trace linearity helpers; five concern unchanged weighted-adjoint linearity/multiplication helpers. These are usable algebraic identities, not assumed conclusions. |
| `opengauss_screener.py <five owners> --strict --json` | Final exit 0, no violations. The first scan misclassified two real-valued trace proofs as unprojected operator arithmetic. Their proof endings now use the native ordered-group lemma `eq_zero_of_neg_eq` directly. The screener is unchanged. |
| `python3 verification/real-matrix-split/audit.py --write`, then without `--write` | Exit 0; 86 explicitly named public declarations in the existing seven-owner inventory. This is source inventory, not a kernel axiom result. |
| `git diff --check` | Exit 0. |
| Workflow YAML, every embedded Bash script, embedded Python blocks | YAML parsed; every `bash -n` returned 0; all three Python blocks parsed. The workflow itself was not executed locally. |
| Independent mathematical/source review | Recovery, trace identities, odd-generator consequences, metric transport, and the real density counterexample were reviewed separately from their authors. No concrete mathematical/API blocker remained. |
| Independent workflow source review | Exact-head selection, dependency pins, fresh outputs, full selected-owner axiom audit and zero-warning guard were reviewed. |

The tracked pre-commit proof gate runs on the staged checkpoint separately
from the checks above. Its actual outcome must be observed before publication;
the presence of the hook is not itself a passing result.

## Native check to be executed

The workflow `.github/workflows/real-krein-cartan.yml` executes the unchanged
maintained checker with these exact targets:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /path/to/pinned-mathlib \
  --lean /path/to/lean-runtime/bin/lean \
  --output /path/to/fresh-verification-output \
  --target InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility \
  --target InfoGeometry.OperatorAlgebra.RealMetricAdjoint \
  --target InfoGeometry.OperatorAlgebra.RealKreinTrace \
  --target InfoGeometry.OperatorAlgebra.RealMetricTransport \
  --target InfoGeometry.Examples.RealKreinDensityCounterexample
```

The paths are runtime locations, not new dependency pins. CI verifies the
exact PR commit, the existing Mathlib revision and toolchain, and the official
Lean archive SHA-256
`47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4` on a cold install.
It hydrates only the current Mathlib import roots under the original shared
build lock, preserves caches, and compiles repository source into fresh
per-run/per-attempt output. It does not pass `--incremental` or `--skip-audit`.

The native audit inspects declarations owned by every selected mathematical
module, including generated declarations, and rejects unsafe/partial
declarations and axiom dependencies outside `propext`, `Classical.choice` and
`Quot.sound`. That list is the acceptance rule; it is not yet an observed
axiom result for this change. The workflow also requires one successful,
zero-warning compile record per selected owner and a report tied to the
exact requested commit. It uploads source snapshots, fingerprints, logs and
native audit output.

## Environment and root-workspace boundary

Local preflight inspected compiler processes and attempted a nonblocking
acquisition of the maintained shared lock. It found an active lock owned by
another `clifford-dirac` transaction. No concurrent compiler/cache process was
launched, no lock was removed or bypassed, and no other process was terminated.

The root Lake workspace separately references absent path packages including
`external_refs/homotopy-hypothesis-lean4` and `external_refs/atlas-lean`. This
change neither invents their revisions nor alters the root manifest or
required gates. The base revision also contains the previously observed
case-colliding `lean/Docs` and `lean/docs` paths, outside this change.

The new workflow provides scoped source-closure verification. It does not
establish a passing root Lake build, completion of the root post-build gate,
or validation of every historical repository file. The PR remains a draft
while these distinct native and integration results are unresolved.
