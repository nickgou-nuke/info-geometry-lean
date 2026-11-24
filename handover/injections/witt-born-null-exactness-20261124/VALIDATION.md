# Validation: Witt modes, Born exchange, and null exactness

## Status

The supplied-table counterexample owner has compiled with warnings as errors
and passed its declaration audit in scoped CI. The full suite has compiled
eight repository modules and stopped at three unused-simp-argument errors in
the determinant owner; full-suite acceptance remains pending. The genuine-Zorn
additions also have independent source review. The scoped GitHub workflow is a
separate check from the repository's existing integration gates.

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

The first expanded checker hash was
`801c1ccf518eb511a24896ec16853e00d9edfa323a5d3d30b4ac33ecfca44c2e`.
It constructs `BuildLock` directly in the context manager. This repairs the
previous double acquisition caused by entering an already-acquired helper
result, while retaining the maintained exclusive lock and child cleanup.
The lock implementation, pins, and staged/push gate implementations are
unchanged. Its changed hash invalidates earlier checker-cache fingerprints.

## CI boundary

The first published workflow is `.github/workflows/zorn-witt-born.yml`, SHA-256
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

## First scoped CI result and bootstrap repair

Run `45408330719`, job `138494989275`, tested merge revision
`43c90beb66cadff1f78f1ca9f19ed2ad967ec988` for PR head
`603faa37744b57392655dbd04f3aae58f027f74b`. Its recorded tree was
`f4462451d67b742a0390f85a71bed39e3d12f217`, the reviewed publication tree.
Checkout, pinned toolchain installation, cache download, and evidence upload
succeeded. The first repository compile failed because
`Batteries.Lean.Position.olean` was missing. No theorem elaboration completed,
no declaration audit ran, and the full suite was skipped.

The downloaded artifact's SHA-256 was
`c8277fb1ee1ee3809473beb7de609ea902df3ab6d58e4b0226e859d4e79fa178`.
Its exact source identity, failing receipt, and native diagnostic are preserved
in `ci-45408330719/`. The artifact is also available from the GitHub run.

Source investigation found that the cache child inherited the repository
working directory: Lake's `-d` selects configuration but does not change the
cache subprocess cwd. Pinned Mathlib cache extraction redirects Mathlib
archives, while other package archives retain cwd-relative destinations.
That explains the missing dependency artifact; the misplaced file itself was
not captured, so its precise previous location remains an inference.

The repair adds an optional working-directory argument to the existing child
runner, retaining the repository default for every current compiler/audit
call. CI now runs cache hydration and a Lake build of the selected native
imports from the actual pinned Mathlib directory, under the maintained lock,
before relocating the fresh dependency checkouts. All pin, manifest,
cleanliness, source-hash, and audit requirements remain in place.

Repaired checker SHA-256:
`26c187c9fe392a441a17f198b9dc9eb90034fa7bdbd4154f8ca6c23f7461bb2b`.
Repaired workflow SHA-256:
`98a55483d5bb3de8043dc3f815c8ead20c785b47907077cdaf01a99b06f10c8d`.
`CI_BOOTSTRAP_REPAIR.md` records the source evidence and exact change. These
repaired bytes still require the next actual CI result; the earlier syntax
receipt is explicitly for the earlier hashes.

## Second scoped CI result and determinant cleanup

Run `45410082037`, job `138501185114`, tested merge revision
`ec4afea58785435e5cdaeb04a509e1a9d85e05eb` for PR head
`878d316cd554fee2742787af7213a219dcff4bbf`. The recorded tree was
`9b702eb72257d4fea51d64044d86b09fcfc8473e`, exactly the published repair tree.
The corrected native dependency preparation succeeded.

The light suite compiled `InfoGeometry.Verification.SuppliedTableCounterexample`
with warnings as errors and passed its axiom audit. It audited **17 declarations**,
including private/generated declarations. Its transitive axiom set was
`[propext, Classical.choice, Quot.sound]`. The receipt run ID is
`f1506feb2d554ce7858c48bf26de8538`; status is `compiled`, audit status `passed`.
This is the first completed native acceptance result for that owner.

The full suite then compiled eight repository modules, including the genuine
Zorn vector-matrix carrier, polarized left multiplication, and the new inverse
owner. It stopped in `ZornLeftDeterminant.lean` because three redundant simp
arguments were reported as errors under the unchanged warnings-as-errors rule:
`Equiv.Perm.sign_swap` at line 121, `Matrix.det_smul` at line 147, and
`zero_add` at line 162. No unsolved proof goals were reported in that owner.
The full-suite receipt run ID is `afe0497bb3334d8f9676c58e5b5a9141`; status is
`failed`, audit status `not-run`. Later modules were not reached, so the light
suite's success does not certify their proofs.

The follow-up source change removes exactly those three unused arguments. It
does not disable linters, alter theorem statements, or weaken any validation
gate. A new native run is required to accept the changed source and continue
the selected dependency closure.

Artifact `14928872917` has SHA-256
`54d34ce36ffc0983cecaeddea95a2de15041b17e71437b1792090d965ccc08d7`.
The exact source identity, both suite receipts, successful light audit output,
and determinant diagnostic are preserved in `ci-45410082037/`.

## Results to record before acceptance

- The completed light-suite receipt and its exact axiom output.
- The full-suite native command results and final declaration audit.
- The exact CI source commit/run and artifact coverage.
- The separate staged/push gate outcomes and any umbrella/root coverage.

No complete-root build, passing publication/merge gate, full Clifford algebra
isomorphism, or physical/geometric classification follows from a source scan
or a passing counterexample check.
