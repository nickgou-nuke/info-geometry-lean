# Klein formalization: verification report

## Acceptance status

**Draft publication with native verification pending.** The reviewed source
candidate has been restored byte-for-byte and committed. The current recovery
uses the exact pinned Lean distribution and Mathlib source. Its first cache
recovery attempt timed out after 600 seconds without acquiring the shared
build lock; no cache or compiler command ran in that attempt. A subsequent
ordinary queued acquisition is in progress at this documentation checkpoint.

The dedicated `Klein crossed product (scoped kernel)` GitHub Actions workflow
will check the exact PR head on an independent runner. Publication as a draft
is not a kernel-acceptance certificate. The repaired three owners still need
the completed native rerun and selected-owner declaration axiom audit below.

Work branch: `codex/klein-crossed-product-20261116`, based on
`08c34e03f610b452e03422037949196dc7d92d6d`. The recovered source tree is
`62ae67e7a9e3ffed9477d49883cdfb91e6f163d7`, locally checkpointed as
`895f01afc7cc62b3337460a60e3a7f85103fb154`; subsequent changes add the focused
CI workflow and its review. The earlier split-spinor PR #363 is separate.

See [the contract](KLEIN_CROSSED_PRODUCT_CONTRACT.md) for precise carriers,
hypotheses, existing owners, corrections, and open mathematical boundaries.
See [the review](KLEIN_CROSSED_PRODUCT_REVIEW.md) for independent inspection
of the original candidates and the subsequent compiler repairs.

## Source scope

| Mathematical owner | New theorem declarations | New definitions |
| --- | ---: | ---: |
| `Algebra/SkewPolynomialFactorization.lean` | 5, including one private helper | 0 |
| `Algebra/QuadraticCrossedProduct.lean` | 22 | 9 |
| `Algebra/CARTwoSidedIdeal.lean` | 8 | 1 |
| Existing `OperatorAlgebra/Z2ProjectorWeights.lean` | 4 | 0 |
| **Total** | **39: 38 public and one private** | **10** |

These are source-declaration counts, not counts from a completed axiom audit.
The entire changed projector owner, including its ten pre-existing theorems
and three definitions, is selected for checking. `InfoGeometry.All` imports
the three new modules. The maintained scoped checker selects four owners and
their exact ten-module repository source closure.

## Completed validation

| Check | Observed result | Actual scope |
| --- | --- | --- |
| Independent mathematical and pinned-API reviews | Passed | Different reviewers inspected authors' candidates, compiler repairs, and final source/documentation consistency. |
| Strict placeholder audit of the final four owners | Exit 0 | No hard findings; soft lexical findings were reviewed. |
| Final semantic vacuity gate, blocking level `error` | Exit 0 | Two reviewed warning-level findings remain. |
| Final OpenGauss screener with `--strict` | Exit 0 | No reported violations. |
| Installed staged proof gate during the source checkpoint commit | Exit 0 | Actual output: `proof_proxy_staged_gate: ok`; staged source and aggregate import checks ran. |
| `git diff --check` and `git diff --cached --check` | Passed at checkpoint | Source-format checks, separate from compilation. |
| Recovery checkpoint staged proof gate, 2026-11-17 | Exit 0 | The actual hook accepted the restored eight-file source snapshot. |
| Focused CI source and syntax review | Passed | Independent review, YAML parse, Bash syntax, and embedded Python AST; not an executed workflow result. |

The two remaining semantic warnings concern `matrix_trace` and the unchanged
`AlgHom.map_projectorWeight`. These compute the actual matrix trace and
preservation of a projector expression by an algebra homomorphism. Their
short proofs are substantive. An earlier warning about
`traceCoefficient_fixed` disappeared after a necessary native proof repair;
proofs were not padded to avoid lexical findings. Three unused definitional
coercion aliases were removed during source review.

The first warning-level semantic scan and first OpenGauss scan failed.
Historical results are retained separately from the later successful scans.
`final-static-gates.json` records the complete argument arrays, exit codes,
and hashes of the exact repaired sources.

## Historical native compiler observations, 2026-11-16

The first ordinary maintained-checker pass obtained the lock and checked all
ten modules. Seven modules compiled successfully. This included the new
`CARTwoSidedIdeal` owner with zero warnings. Seven warnings appeared in two
unchanged dependencies: five in `SplitCliffordAlgebras` and two in
`CPTComplexStructure`.

Three selected owners failed that first pass:

- The skew-polynomial coefficient proof needed the product-to-monomial rewrite
  before simplification could expand the constant subtraction.
- The quadratic matrix proofs needed explicit instances of the involutivity
  hypothesis and a `map_zero` rewrite. Unused simplifier arguments were removed.
- The two projector equivalence proofs needed an explicit `sub_eq_zero` rule.

The reviewed repairs were integrated without changing theorem statements,
carriers, assumptions, or multiplication order. The first pass did not reach
its axiom audit. Its source snapshots, report, and module logs are archived
under `first-native-pass`; those old failures are not a check of the repaired
proof bodies.

An ordinary incremental rerun waited for the lock, but its tool session later
became unavailable without new compiler results. The subsequent bounded
retry also could not acquire the lock and returned the explicit 600-second
wait error above. The latest report fingerprints the repaired source closure,
but contains no compilation result. Retained module logs from the first pass
must not be mistaken for new diagnostics on those repairs.

## Environment and reproducible command

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Dependency/toolchain pins and maintained checker sources were not changed.
- The previous session hydrated the required cache without deleting cache roots; the restored session must recover those missing artifacts again.

The ordinary maintained command, from the repository root, is:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/ecf0f7649d13/pinned-mathlib \
  --lean /workspace/scratch/ecf0f7649d13/lean-runtime/bin/lean \
  --output /workspace/scratch/ecf0f7649d13/verification-klein-20261117 \
  --target InfoGeometry.Algebra.SkewPolynomialFactorization \
  --target InfoGeometry.Algebra.QuadraticCrossedProduct \
  --target InfoGeometry.Algebra.CARTwoSidedIdeal \
  --target InfoGeometry.OperatorAlgebra.Z2ProjectorWeights \
  --incremental
```

The historical final bounded native attempt used
`/workspace/scratch/ecf0f7649d13/verification-klein/retry_shared_lock.py`
as the Python entry point with the same remaining arguments. The full
invocation is recorded in `bounded-retry-launcher.json`. Launcher SHA-256:
`206bf34526f6694aefe9e376902778d22294081629fd0882d4ad1f0b7fab2628`.

An independent review confirmed that this launcher repeatedly calls the
original exclusive lock acquisition on the same lock path. It changes only
contention scheduling: 50 ms retries, periodic notices, and a timeout check
after a failed attempt exceeds 600 seconds. It preserves descriptor handling,
release, inherited lock descriptors, compiler commands, fingerprint/artifact
checks, and the final declaration audit. Its source, hash, and invocation are
included so the custom launcher is explicit; it is not described as an
unmodified invocation. The timeout concerns acquisition retries, not the
running compiler or a fairness guarantee.

The command omits `--skip-audit`. A successful continuation must check every
declaration owned by the selected targets against the allowed foundational
axioms `propext`, `Classical.choice`, and `Quot.sound`. That acceptance step is
still outstanding.

## Current recovery and CI

The fresh checkout is based on the same upstream revision, and the restored
source tree and all four source-check hashes match the saved candidate.
The official Linux Lean archive was downloaded and its SHA-256 verified as
`47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`
before extraction. The independent Mathlib checkout is exactly at the
unchanged pin above. No dependency metadata or maintained checker is changed.

The first cache recovery attempt on 2026-11-17 executed zero cache/compiler
commands because the lock remained occupied. The next request uses the
original blocking lock acquisition, with a deadline only while acquiring
that lock; the deadline is disabled before any compiler process can start.
Neither attempt terminates another holder or bypasses the shared lock.

The focused workflow fetches the exact PR head, checks the same pins and
compiler checksum, derives cache roots from the current source closure, and
runs the maintained four-target command with its native audit enabled. It
uses fresh output for each run and attempt, then explicitly requires zero
warnings in all four selected owners. Logs, reports, source snapshots, and
audit output are retained as a workflow artifact. The workflow and its
review are part of this patch; execution results must be inspected separately.

## Repository build boundary

The earlier split-spinor pre-push attempt observed a missing path package,
`external_refs/homotopy-hypothesis-lean4`. The fresh checkout also lacks that
package and the separate `external_refs/atlas-lean` path package. Their
absence is a current filesystem observation; the earlier failed root gate
is not presented as a new gate execution on this patch.

No completed local root pre-push or full Lake certificate is claimed for
this draft. A passing scoped workflow would still cover only the selected
owners and their exact source closure, not every declaration imported by
`InfoGeometry.All` or every repository target. The existing root hooks and
quality workflows remain unchanged. No missing dependency URL or revision
has been invented.

The next acceptance step is to inspect a completed current native compilation
and declaration axiom audit, repair any concrete failures, and bind the result
to the published source. All preceding failed attempts remain historical
evidence, not substitutes for that successful result.
