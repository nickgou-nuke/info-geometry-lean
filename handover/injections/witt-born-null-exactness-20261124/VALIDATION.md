# Validation: Witt modes, Born exchange, and null exactness

## Status

The genuine-Zorn additions have independent source review. Native elaboration
and axiom acceptance of those additions remain pending. The scoped GitHub
workflow is a separate check from the repository's existing integration gates.

## Local retry of the prior Klein closure

The retry started at 15:30:33 Europe/Sofia on 2026-11-24, before integration of
the new Witt/exactness source changes:

```bash
python3 verification/zorn-primal-dual/check.py \
  --suite klein-operator-hierarchy \
  --lean /workspace/scratch/058543be00a5/lean-runtime/lean-4.34.1-linux/bin/lean \
  --packages /workspace/scratch/058543be00a5/info-geometry-lean/.lake/packages \
  --no-wait-for-build-lock --force
```

The maintained build lock was available. The first native compiler command,
for the existing `InfoGeometry.Algebra.ZornVectorMatrix`, terminated with
**return code -9 (SIGKILL)** after **343.817 seconds**. It emitted no Lean
diagnostic. The invoking command reported process exit 247. No repository
module completed and no axiom audit ran. The receipt alone does not identify
the source of the signal; it is not a theorem counterexample or syntax error.

Exact receipt: `failed-native-check.json`.
Run ID: `14af0762cf8f4e7aa8f0fe3995cc0da3`.
Receipt status: `failed`; audit status: `not-run`.
This attempt used the prior checker hash
`293bd44367d8594ae9f51d8f9a148ca90e8a28cc8fa61e112aa3e5658a7a2ca5`.

## Current native checking surfaces

The light suite was also attempted locally at 15:41:48 Europe/Sofia on
2026-11-24, with the same explicit compiler and package arguments. Its single
compiler command was killed with return code **-9 (SIGKILL)** after
**290.9 seconds**, without a Lean diagnostic. No module completed and the
axiom audit did not run. The invoking process again reported exit 247.
The sampled peak RSS was 232,104 KiB; this sampling and the signal do not
establish why the process was killed.

The exact second receipt is `failed-counterexample-check.json`, run ID
`af0993eddf70468fa6d7ddd3f7221441`. It records `status: failed` and
`audit_status: not-run`. The counterexample source is therefore still
source-reviewed, not locally kernel-verified.

The expanded checker retains the original suites and adds:

```bash
python3 verification/zorn-primal-dual/check.py --suite supplied-zorn-counterexample
python3 verification/zorn-primal-dual/check.py --suite witt-born-null-exactness
```

Pass `--lean` and `--packages` when the compiler/cache is outside the checkout.
The light suite selects only the supplied-table integer counterexample owner.
The full suite selects 11 targets and traverses 50 repository modules. All
12 task-owned modules compile with warnings as errors. Its declaration audit
covers 15 owners, including the reused native Clifford representation and
the previous noninjectivity and groupoid checks.

Both audits enumerate private/generated declarations, follow transitive axiom
dependencies, reject unsafe/partial declarations, require each selected owner
to contribute declarations, and allow only `propext`, `Classical.choice`, and
`Quot.sound`. The integer counterexamples do not certify the genuine Zorn
operators; each suite has its own result.

The current checker hash is
`801c1ccf518eb511a24896ec16853e00d9edfa323a5d3d30b4ac33ecfca44c2e`.
It constructs `BuildLock` directly in the context manager. This repairs the
previous double acquisition caused by entering an already-acquired helper
result, while retaining the maintained exclusive lock and child cleanup.
The lock implementation, pins, and staged/push gate implementations are
unchanged. Its changed hash invalidates earlier checker-cache fingerprints.

## CI boundary

The final workflow is `.github/workflows/zorn-witt-born.yml`, SHA-256
`e746f31072307210f33b722d41b95ebbc77de51a6749c48cc5e4f551593c4d32`.
Its independent review is in `CI_REVIEW.md`. The exact workflow bytes passed
YAML parsing, syntax checks for all seven shell blocks, and AST parsing for
all four embedded Python blocks. The checker Python AST also parsed.
`static-check.json` preserves this syntax-only result; none of those checks
executes Lean or the GitHub workflow.

A later attempt to check optional extra provenance fields was blocked by
another task holding the shared build lock. Those optional fields were
removed by restoring the exact already-reviewed and syntax-checked workflow
bytes above. `blocked-static-recheck.json` records that event. No staged
proof-gate attempt began in this continuation while that lane was occupied.
The full precommit/prepush gate status therefore remains pending.

For a pull-request event, `GITHUB_SHA` denotes the merge-test revision. The
workflow records that exact revision/tree and run identity; any CI result
must be reported at that recorded scope, not silently as a full root or
unrelated branch certificate.

At the previous PR head `e46d5bc01d977887edc3f0089ad76fe300f158fa`, GitHub CI
run `45378304649` failed at `Validate local Lake package checkouts`, before
the baseline build. Other scoped jobs' statuses do not establish validation
of these new owners. A dedicated scoped workflow prepares only the exact
native dependency environment required by this check and preserves its
receipts. It does not waive or replace any required repository gate.

## Results to record before acceptance

- The completed light-suite receipt and its exact axiom output.
- The full-suite native command results and final declaration audit.
- The exact CI source commit/run and artifact coverage.
- The separate staged/push gate outcomes and any umbrella/root coverage.

No complete-root build, passing publication/merge gate, full Clifford algebra
isomorphism, or physical/geometric classification follows from a source scan
or a passing counterexample check.
