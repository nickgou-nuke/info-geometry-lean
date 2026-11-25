# Validation: Witt modes, Born exchange, and null exactness

## Status

The supplied-table counterexample owner has compiled with warnings as errors
and passed its declaration audit in three consecutive scoped CI runs. The
latest strict full suite compiled nine repository modules and stopped in the
primal/dual owner. The isolated diagnostic continuation then visited all 50
modules: 42 elaborated in diagnostic mode, five had errors, and three were
skipped because an import failed. Diagnostic results do not establish proof
acceptance. Repairs for the observed errors and owned warnings have source
review; the full strict build and declaration audit remain pending.

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

## Third scoped CI result and primal/dual repair

Run `45413662613`, job `138513918858`, tested merge revision
`298b64789e099dbeb457e8862cdd4d31413388e1` for PR head
`0db6e19eadcfffbfc468138a25d88ff7bef326fb`. The recorded tree was
`4c995f372ac7f775188f66dd42bc2a7a2b8d924e`, exactly the published cleanup tree.
Pinned dependency preparation and the 17-declaration counterexample audit
passed again. The light receipt run ID is `6ef41b82b0924986ae380dbb4b1c77ac`.

The full suite compiled nine modules, including `ZornLeftDeterminant` with
warnings as errors. It then failed in `ZornPrimalDual`: `encode.map_smul'`
left an identity-ring-hom scalar normalization goal, and the mixed-product
helper left projections of native carrier subtraction unreduced. The
downstream `norm_encode` declaration was consequently marked as depending on
the failed definition's generated placeholder; no source `sorry` was inserted.
Two square proofs also had an unused `Fin.sum_univ_three` argument. The full
receipt run ID is `8b0e3c0135d84076b86bb0015b70fc6a`; status is `failed`, and
the full declaration audit remains `not-run`.

The source repair adds `RingHom.id_apply` to the exact scalar-normalization
step, removes the two reported unused sum arguments, and rewrites the intended
native carrier difference with `_root_.sub_eq_add_neg` before coordinate
extensionality. It uses the carrier's existing native negation projection
lemmas, removing the unrelated explicit `sub` and `neg` definitions from that
simp list. Statements and mathematical conventions are unchanged. See
`CI_PRIMAL_REPAIR_REVIEW.md` for the source review.

Artifact `14931587245` has SHA-256
`e0f6d4303538e6f4dd0144477ef5ff929ffd1ca1c464113071d30482d5976fa2`.
Its exact source identity, both receipts, light audit output, and primal/dual
diagnostic are preserved in `ci-45413662613/`.

## Isolated diagnostics after strict failure

The repeated early source failures justify collecting later diagnostics in
the same CI run. `verification/witt-born-null-exactness/diagnose.py` is a
separate, explicitly nonaccepting runner. It requires a matching failed strict
full-suite compile receipt, uses a fresh UUID output library, and checks the
same pinned compiler, sources, and dependencies. It retains ordinary warnings,
records actual Lean errors, and skips descendants of failed modules while
checking independent branches. It neither consumes nor updates the strict
compilation caches and does not run the acceptance audit.

Every diagnostic result has `acceptance: false`; the runner always exits
nonzero. CI invokes it only after the strict full-scope step fails. The strict
checker, its warnings-as-errors policy, axiom audit, and receipt-acceptance
conditions are unchanged. A failed strict check therefore remains failed.
`DIAGNOSTIC_DESIGN.md` preserves the authored design snapshot, and
`DIAGNOSTIC_REVIEW.md` records independent source review. Those reviews alone
do not establish that the new runner has executed successfully.

Diagnostic runner SHA-256:
`46464783b6c273365688fd38bf19dd3dcd544cfbf9e60efe165922712f516ce7`.
Integrated workflow SHA-256:
`91717dc7c280174c91f55a4c23c9925c5c5254861ba1e1da6ac01f3e3449a9b2`.
Repaired primal/dual owner SHA-256:
`e2705577751f0759455f8caecb1ba9481a109b39c409ca0a52ebd93615eab128`.

The exact updated workflow passed YAML parsing and `bash -n` for all eight
shell blocks; its embedded Python and the diagnostic runner passed AST parsing.
The maintained exclusive build lock covered these checks. The first staged
gate invocation used an unsupported CLI flag and was rejected before scanning;
after correcting that invocation, the current staged primal/dual source passed
`python3 tools/quality/proof_proxy_staged_gate.py --strict
lean/InfoGeometry/Algebra/ZornPrimalDual.lean`. The exact invocations and results
are in `primal-diagnostic-source-check.json`. This is a source-gate result for
that staged owner, not native elaboration, a push-gate result, or validation of
every earlier PR owner. The final staged whitespace check also passed; the
verbatim compiler output is preserved inside `primal-dual-diagnostic.json` to
retain its whitespace without introducing whitespace errors in the Git patch.

## Fourth scoped CI result and batched native repairs

Run `45416776463`, job `138525022894`, tested merge revision
`4fdd01ba6f8923482423b4a7838fe1f037b955c9` for PR head
`c97caca572514f128e846212ca30f050414dabac`. Its recorded tree
`8b16b335faf643bedb2eb3884d13cb73a04a6c28` matched the published tree.
Pinned preparation and the 17-declaration light-suite audit passed again.

The strict checker accepted the same nine-module prefix, then stopped in
`ZornPrimalDual`. The identity-hom repair succeeded. Its mixed helper now
exposed explicit Zorn negation projections, which require unfolding the
explicit negation function after the native-subtraction rewrite. The previous
source-only judgment that native negation projection lemmas alone would
suffice was incorrect for this intermediate expression. `norm_encode` also
reported an unnecessary `<;>` tactic sequence.

The isolated runner completed its intended diagnostic pass. It recorded
`status: diagnostic-complete`, `acceptance: false`, and exited with code 2.
It did not run an axiom audit or modify the strict result. Its run ID is
`c73ae23678dd44f398d46c2a8ef7184f`. The complete 50-module result comprised
42 ordinary-mode elaborations, five error owners, and three skipped owners.

The six affected owned files are repaired as follows:

| Owner | Actual diagnostic and focused repair |
| --- | --- |
| `ZornPrimalDual` | Restore explicit negation unfolding after the root subtraction rewrite; use ordinary sequencing for the norm proof. |
| `ZornChiralOperatorReconstruction` | Fix the intended real carrier on the applied operator difference and witness value; remove the reported redundant finite-sum argument. |
| `SouriauAffineActionGroupoid` | Use the recommended instance-reducibility attribute and the current root `add_apply` declaration. Its diagnostic elaboration otherwise succeeded. |
| `SouriauCotangentGraphSigns` | Normalize the coefficients at `c=1` and `c=-1`, and normalize `(-1) • B` to `-B`; the exact coefficients stay `-1` and `3`. |
| `ZornNullIncidence` | Expose the explicit zero expected by contraction/conjugation lemmas, give rank arithmetic common typed dimensions, and use the recommended local `let` bindings. |
| `ZornCliffordKleinHierarchy` | Reduce the gamma application before readback, prove the chirality scalar law abstractly, distribute scalar actions/products before additive rearrangement, and use the recommended local `let` bindings. |

The real carriers, nonzero/null hypotheses, nonassociative witness, polar
normalization, and theorem contracts are preserved. In particular the
bivector proofs continue to use the actual noncommutative endomorphism ring;
`abel` rearranges sums only after multiplication order has been fixed by
associativity and distribution. No linter or acceptance check is disabled.
The five `CI_*_NATIVE_*REVIEW.md` records preserve the authored and independent
source reviews, including exact source hashes.

`ZornCliffordSourceVolume`, `SplitOctonionNullPlaneCovariance`, and
`ZornCliffordWittBorn` were skipped because imports failed. Their unchanged
source therefore still requires native elaboration and audit; the diagnostic
pass gives no acceptance result for them.

Artifact `14933636941` has SHA-256
`f4ce652d5505c553567b12428c33417f070615e102eccb26b6d4ae4a23545df2`.
`ci-45416776463/` preserves the exact source identity, light/strict receipts,
light audit output, and exact affected-owner diagnostic strings. Its compact
diagnostic receipt is explicitly marked as derived and includes the original
full-report hash plus every module outcome. The original complete diagnostic
report and logs remain in the referenced artifact.

The transient `/tmp` checkout became unavailable after this run. All tracked
work had already been published and the worktree was clean. An independent
sparse checkout was restored under the workspace at the exact same `c97caca`
head, preserving the 50-module source closure and tooling. No dependency pin,
cache, or existing source was deleted as a repair.

The exact six-owner batch passed staged whitespace review. Its strict staged
source-gate attempts were blocked before scanning by another task holding the
maintained build lock. `batch-native-source-check.json` records both attempts
and every staged owner hash. The earlier passing single-owner source gate
does not certify this changed batch. No local native retry or passing push
gate is claimed for it; the existing PR remains a draft pending validation.

## Results to record before acceptance

- The completed light-suite receipt and its exact axiom output.
- The full-suite native command results and final declaration audit.
- The exact CI source commit/run and artifact coverage.
- The separate staged/push gate outcomes and any umbrella/root coverage.

No complete-root build, passing publication/merge gate, full Clifford algebra
isomorphism, or physical/geometric classification follows from a source scan
or a passing counterexample check.
