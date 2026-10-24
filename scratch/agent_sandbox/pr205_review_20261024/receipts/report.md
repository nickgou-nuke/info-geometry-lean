# Task #17 — PR #205 CI and verification-claims review

Reviewer: `acceptance_receipt_review`

Review date: 2026-10-24, approximately 08:45–08:49 UTC

Scope: read-only source/CI receipt inspection; no compilation, testing, gates, checker execution, branch change, merge, or remote comment.

## Disposition

**The public CI success is substantiated; the claimed artifact contents are not independently inspected here.** No current-head false-success defect was demonstrated by this source review. There is a real future CI trigger-coverage gap, plus several narrower verification hardening opportunities. These do not justify describing the observed successful run as failed.

- GitHub API confirms PR #205 is open/unmerged, with eight added files, 847 additions and no deletions.
- Run **40077004618**, attempt 1, and job **120822411313** (`kernel-check`) completed successfully. The compile/audit step and artifact upload step both succeeded.
- The exact PR head and reported merge checkout revision have **identical Git trees**. This is stronger evidence than merely assuming `head_sha` is the checked-out commit.
- All eight downloaded PR files independently match the Git blob IDs in the files API metadata. Their bytes also match public raw files at the merge revision.
- Textual counts are **31 named theorems, 12 named definitions, and 6 `#check` commands**. The claimed **73 generated-plus-named audited declarations** is not a textual count and remains unconfirmed without audit contents or the parent's independent replay.
- One unexpired artifact exists with public digest metadata. Archive download returned **HTTP 401**; job-log download returned **HTTP 403**. No artifact contents, audit count, warning totals, `status.json`, source-closure manifest, or executed `lean --version` output are claimed inspected.
- The checker builds the repository import closure and audits declarations attributed to **five selected new modules**, including transitive axiom dependencies. It is **not** an independent imported-proof kernel replay, a strict all-declarations audit of the entire closure, a semantic trap screen, or a full root Lake build. The contract correctly limits the root-build claim.

The prior task-14 report is retained unchanged. This report concerns PR #205's exact source snapshot, not the dirty working-tree owners reviewed in task #14.

## 1. Provenance and public API evidence

### PR and revisions

Local metadata read:

- `/tmp/pr205-api.json`
- `/tmp/pr205-files.json`
- `/tmp/pr205-ci-run.json`

Exact source snapshot: `/tmp/pr205-review-ea08baa/`.

| Item | Value |
|---|---|
| Repository | `nickgou-nuke/info-geometry-lean` |
| PR | `https://github.com/nickgou-nuke/info-geometry-lean/pull/205` |
| Head | `ea08baa1649c9eeaf45638d6e7edef2f971ad1be` |
| Base | `21189e55133ed207043f2f05e37aa52d1fc8a9f5` |
| Reported merge revision | `01c872dd32ebd50cc8f72f09e32067df2de40caf` |
| Head and merge tree ID | **`895f1f864aa45b23aec57ccde1a30bc424b3fad0`** |

Public Git commit API requests confirmed the merge parents are the stated base and head. The head and merge commit have the same tree ID, so their complete versioned source trees agree. This resolves the apparent distinction between Actions run metadata `head_sha` and workflow `SOURCE_REV: ${{ github.sha }}` for this run's reported merge revision. The actual checkout step log remains unavailable, so the exact executed checkout SHA is supported by workflow semantics and the supplied revision rather than a retrieved checkout transcript. No source discrepancy exists between those two candidate revisions.

API URLs consulted read-only, without credentials:

- `https://api.github.com/repos/nickgou-nuke/info-geometry-lean/actions/runs/40077004618`
- `https://api.github.com/repos/nickgou-nuke/info-geometry-lean/actions/runs/40077004618/jobs`
- `https://api.github.com/repos/nickgou-nuke/info-geometry-lean/actions/runs/40077004618/artifacts`
- `https://api.github.com/repos/nickgou-nuke/info-geometry-lean/git/commits/ea08baa1649c9eeaf45638d6e7edef2f971ad1be`
- `https://api.github.com/repos/nickgou-nuke/info-geometry-lean/git/commits/01c872dd32ebd50cc8f72f09e32067df2de40caf`

### Run, job and artifact

Run metadata, independently refreshed during this review:

- Name: `Peirce Weyl trace (scoped)`.
- Event: `pull_request`.
- Workflow path: `.github/workflows/peirce-weyl.yml`.
- `head_sha`: `ea08baa1649c9eeaf45638d6e7edef2f971ad1be`.
- Status/conclusion: `completed` / `success`.
- Created 2026-10-24 08:10:32 UTC; recorded update 08:13:57 UTC.
- One returned job: `kernel-check`, ID **120822411313**, completed successfully at 08:13:56 UTC.
- Checkout step, toolchain installation, compile/audit step, and upload step all report `success`. The compile/audit step ran 08:11:11–08:13:53 UTC.

One artifact returned:

| Field | Value |
|---|---|
| ID | `12552794453` |
| Name | `peirce-weyl-verification` |
| Size | `67786` bytes |
| Expired | `false` |
| Created | `2026-10-24T08:13:54Z` |
| Expires | `2027-01-22T08:10:32Z` |
| API digest | `sha256:cfc8807ad8f68275194e7eb490e5d75cc99d5a17b85d015929a48ead1741923a` |
| Associated run/head | `40077004618` / stated head |

The artifact API response bytes had SHA-256 `2d6bd9d9851f37b807f1a96ed2f7417b25c24d2bb23848ed1c9275f7c7e496e9`; the jobs response bytes had SHA-256 `be0268daa2e555f6253048619e899d352b764df61cd8b0f667f9d317e85d51fd`. These hashes identify the responses observed by this reviewer, not artifact bytes downloaded or authenticated independently against the advertised artifact digest.

Unavailable content requests:

- `.../actions/artifacts/12552794453/zip`: **401**.
- `.../actions/jobs/120822411313/logs`: **403**.

Public artifact existence/digest and successful upload are evidence of an artifact, not proof of its expected internal files or the asserted count 73. No unavailable sandbox attachments were inferred from summaries.

## 2. Exact source and tool/pin bindings

All eight files were read in full. Git blob matching used the ordinary `SHA1("blob " + byte_length + NUL + bytes)` encoding against the API `sha`; all eight matched. Every file below also matched its raw bytes at the merge revision.

| PR-relative file | SHA-256 |
|---|---|
| `.github/workflows/peirce-weyl.yml` | `155bec3a8bcad22aecd4386e9d0379da97f6a897a578e2a67d800386a1cc77db` |
| `docs/PEIRCE_WEYL_TRACE_CONTRACT.md` | `48ec84399c3689358ace4cb5b06cd18841b1ff86313a88089c07ab3eee30ffbc` |
| `lean/InfoGeometry/Canonical/PeirceWeylExamples.lean` | `e0efd82ddb23726181a1007a421a75ee993af8e19133e960c3de4a1a697f24b2` |
| `lean/InfoGeometry/Canonical/PeirceWeylSynthesis.lean` | `d305cc810f13a28520975f492a708bbeb1a51e69cf065fbe9a4c4fea9502a208` |
| `lean/InfoGeometry/Core/JordanMultiplicationClosure.lean` | `7a4bbf9a9c072f181b5fed9efc9e6fed3b4d6120d48f4435292001d0008cb5ba` |
| `lean/InfoGeometry/Core/PeirceDensityIntertwining.lean` | `6fd7d487455bdc8bfec1a47c130cd61816eeb262bc8c8f6a3daa3e0112486095` |
| `lean/InfoGeometry/Core/PeirceWeylUnits.lean` | `5eb71d9838b58c30f823b772f6b6d953ee2f625e44089fe6586e15a113f97fe9` |
| `tools/quality/check_peirce_weyl.py` | `0277f2f829632f6816831be440c939caf6cd765c6eb686c8d97af0d4b6b1f394` |

Exact-head public raw sources additionally inspected, without saving new files:

- `tools/quality/check_reviewed_prs.py`, full helper read, SHA-256 `7bb54f7cb08fcb933b5619e57d12e0f267ec937abcebd4302c453fd3a54f2ab8`.
- `lean-toolchain`: `leanprover/lean4:v4.34.1`; SHA-256 `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b`.
- `lake-manifest.json`: Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`, URL `https://github.com/leanprover-community/mathlib4.git`, input revision `v4.34.1`; manifest SHA-256 `26d251175b18b53609698c563701d4c08ad323506d5c3087f914dd14965546da`.

Those three helper/pin files also matched merge-revision raw bytes. The inherited helper's private collector implementation is **not used** by the new checker: only `closure` is imported. The new checker's own `audit_source` uses public `Lean.collectAxioms`.

Read-only source-import navigation followed 20 `InfoGeometry.*` files from the Examples target, plus the referenced `DAG.Basic`. This establishes concrete unchanged owners that matter to trigger coverage, not a compiler-derived complete dependency graph. The helper resolves repository files before accepting Mathlib/native imports, and the new modules use ordinary column-zero imports recognized by that helper. No executable helper/checker function was imported or run during this review. Native Mathlib cache contents and actual compiled import resolution were not independently inspected.

## 3. Count reconciliation

| New module | Named `theorem` heads | Named `def` heads | `#check` commands |
|---|---:|---:|---:|
| `Core.PeirceWeylUnits` | 12 | 5 | 0 |
| `Core.PeirceDensityIntertwining` | 6 | 2 | 0 |
| `Core.JordanMultiplicationClosure` | 4 | 1 | 0 |
| `Canonical.PeirceWeylSynthesis` | 1 | 0 | 0 |
| `Canonical.PeirceWeylExamples` | 8 | 4 | 6 |
| **Total** | **31** | **12** | **6** |

The sources have 43 explicitly authored theorem/definition heads. The six `#check`s merely check names/types; they are neither six extra theorem declarations nor an axiom audit. Generated declarations/auxiliaries can increase an imported-environment count beyond 43. **73 is plausible but not established by this review**: it must be confirmed against actual `AUDIT_DECL` lines/count or the parent's independent compiled-environment enumeration. Subtracting 43 from a reported 73 does not independently establish the existence or cleanliness of 30 generated declarations.

## 4. What the checker really enforces

References below are to the exact-head `tools/quality/check_peirce_weyl.py` unless another file is named.

### Compilation, provenance, and process control

- Lines 85–93 read root manifest/toolchain, record checkout revision, require the separate Mathlib checkout HEAD to equal the manifest revision, and require its toolchain text to agree.
- Lines 94–106 compute a repository source-import closure and copy its exact source bytes into an output source tree while hashing those bytes. This binds the report to the **copied** source snapshot; it is not just a filename list.
- Lines 107–118 acquire `/tmp/info-geometry-build.lock`, reject observed `lean`, `lake`, or `leanc` processes, fetch pinned Mathlib cache, derive `LEAN_PATH` from that Mathlib checkout, prepend the new output library, and record `lean --version`.
- Lines 119–131 compile every ordered repository module into that output library and reject any nonzero compiler exit. Logs and each return code are retained.
- The workflow uses fresh runner directories, fetches the project revision and Mathlib pin, and does not initialize unrelated external submodules. This is consistent with scoped source-closure verification, not dependency pin mutation.

### Imported-environment axiom audit

- Lines 31–64 generate an audit module importing all five targets together.
- Lines 46–50 enumerate `env.constants`, resolve each declaration's module index, and retain exactly declarations attributed to the selected target modules. This is stronger than namespace-prefix matching or a handpicked theorem list, and can include generated/private declarations visible in that imported environment.
- Lines 51–58 reject selected declarations marked unsafe/partial and reject every transitively collected axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
- The checker checks transitive **axioms** of target declarations, not every unused declaration in every imported owner. It does not separately reject unsafe/partial declarations throughout the entire unchanged closure.
- Imported `olean` proofs are not explicitly replayed with `Kernel.Environment.replay` here. Source compilation followed by imported-environment collection is distinct from an independent strict kernel replay. The parent's planned replay is additional evidence, not something already supplied by this script.
- Line 61 rejects only an **aggregate** zero count; lines 135–138 require audit process success and presence of `AUDIT_COUNT:` before setting `status='passed'` and `axiom_audit_passed=True`.

### Failure behavior

Ordinary failures in manifest parsing, pin checks, recognized import resolution, copying, lock/process checks, cache fetch, compilation, or the Lean audit raise exceptions; lines 140–144 set failed status and rethrow, then write `status.json`. The shell has `set -euo pipefail`. `if: always()` on artifact upload preserves failure evidence but does not turn a failed compile step into a successful job.

Output-directory creation happens before the `try`, and cancellation/hard termination can prevent a final status file; those conditions do not produce a checker success exit. Fresh CI output makes stale success-receipt reuse less concerning than it would be for arbitrary local reruns.

## 5. Actionable findings, with calibrated severity

### F1 — Medium: real CI trigger-coverage gap, not a failure of this run

**Location:** `.github/workflows/peirce-weyl.yml:3–11`.

The pull-request path filter covers only the five new modules, the new checker, and its workflow. It omits:

- `tools/quality/check_reviewed_prs.py`, whose `closure` implementation is executed;
- `lean-toolchain` and `lake-manifest.json`;
- existing imported owners, including `Core.DiracSuperalgebra`, `Core.JordanAssociatorRing`, `Singular.SquareZeroChiralHodge`, the MP owners, and their further repo dependencies;
- the new contract document (relevant if CI is intended to validate receipt/promise changes).

A later PR modifying only a pin, the imported helper, or a reused owner will not automatically schedule this scoped workflow. That is a concrete regression-coverage gap even though this PR's added target paths triggered the observed run. `workflow_dispatch` offers a manual workaround, not automatic changed-path coverage.

**Action:** add helper/pin paths and conservatively cover repository Lean sources (`lean/**`) or maintain a dependency-aware trigger strategy. Add contract/docs coverage only if contract changes are intended to trigger this check; docs omission alone is not a mathematical bug. No claim is made that other repository workflows fail to cover those paths.

### F2 — Low/medium hardening: aggregate-only audit count cannot demonstrate five-module coverage

**Location:** checker lines 43–63 and 135–138.

The generated audit has one count for all targets. It does not require a positive count for each target module, assert expected public declaration heads, or persist parsed totals/per-module counts in `status.json`. If one target became empty or module attribution unexpectedly omitted it while another remained nonempty, the aggregate guard would still pass. It also does not enforce the advertised total 73.

This is a **latent coverage weakness**, not evidence of a missed declaration at this head: all five current files visibly contain definitions/theorems, and the code imports all five. Do not claim a demonstrated module-omission failure without the actual environment receipt.

**Action:** track counts by originating module, require all five expected owners to appear with positive counts, compare against the intended exported heads, parse one well-formed positive `AUDIT_COUNT` line, and put numeric count/map into the JSON. Avoid freezing incidental generated-declaration counts as mathematical invariants without a versioned expectation.

### F3 — Claim boundary: warnings are accepted and not summarized

**Location:** checker lines 123–138; workflow compile step lines 51–57.

The checker treats compiler exit status as the compile verdict. It neither enables warnings-as-errors nor counts warnings in `status.json`; stdout/stderr are logged. A successful source-closure check can therefore include warnings. Unused inherited `sorry` declarations, if any, could warn without contaminating a target's transitive axiom closure; actual reachable `sorryAx` would be rejected by the selected declaration audit.

**Action:** describe the receipt as “compile and selected-owner transitive axiom audit passed,” not “zero warnings” or “zero findings of every kind.” If policy requires zero warnings, add an explicit narrowly scoped warning policy/count, keeping inherited warnings distinct from new-module warnings. This is **not a blocker under the current contract**, which does not promise warning-free output. No warning count from this run is known here.

### F4 — Low hardening: source/pin identity is good for fresh CI but not a complete hostile/local-worktree attestation

**Location:** checker lines 85–118; workflow lines 26–50.

Mathlib HEAD and toolchain-file equality are checked, and copied repository source hashes are recorded. The checker does not verify clean project/Mathlib worktrees, reject all local Mathlib source/artifact mutation, assert the printed Lean binary version against the requested version, or hash the executing helper/checker and pin files into `status.json`. It records source bytes once, before compilation; it does not rehash the copied tree afterwards. Output `src` and `lib` are created with `exist_ok=True`, allowing reuse by local callers.

The hosted workflow creates fresh directories and installs the declared toolchain, mitigating these concerns for the observed run. The shared head/merge tree also closes that provenance ambiguity. **No current source or tool substitution was observed.**

**Action:** for durable local acceptance receipts, record checker/helper/manifest/toolchain hashes and actual Lean version; require or explicitly report clean pinned sources; use a fresh output directory or refuse a populated output tree; optionally rehash the compiled source snapshot. Do not delete shared caches or discard unrelated work to enforce cleanliness.

### F5 — Low hardening: inherited import scanner is lexical, not Lean's parser

**Location:** exact-head `tools/quality/check_reviewed_prs.py:24–53`, especially lines 35–46.

`closure` recognizes only lines starting exactly `import `, splits inline `--` comments, resolves local `lean/` files first, then accepts Mathlib and Lean/Std/Init prefixes. It does not parse block comments, indented imports, or alternate import syntax such as `public import`. Cycles and unresolved recognized nonnative imports fail closed. All five new owners use recognized column-zero imports; bounded navigation found ordinary imports in their inspected existing-owner chain too.

In a fresh isolated build, a genuinely omitted repo dependency will ordinarily cause compilation to fail rather than silently certify it. A reused output library makes stale resolution more relevant. This is **not a demonstrated incomplete closure in this run**.

**Action:** use a compiler-backed dependency resolver or robust comment-aware import parser, and preserve fresh output isolation. Do not change source imports merely to satisfy the scanner.

### Optional supply-chain nit, not a theorem/receipt blocker

**Location:** workflow lines 47 and 58.

The elan installer is downloaded from a moving `master` URL and the upload action uses `@v4`, not immutable hashes. The Lean toolchain and Mathlib revision themselves are pinned. Pinning the bootstrap installer/action is ordinary CI supply-chain hardening, not evidence that this run used an incorrect prover or that the Lean statements are false.

## 6. Contract and scope assessment

`docs/PEIRCE_WEYL_TRACE_CONTRACT.md` explicitly distinguishes the finite algebraic theorem chain from broader physical/geometric interpretations and disclaims a root-package/all-green CI result. It also says the workflow result/artifact, not the prose document, provide acceptance evidence. That is appropriately calibrated.

The source uses existing native MP/support owners, native `Aˣ`, `LinearMap`, and `Module.End`, and states explicit assumptions. This receipt review does not substitute for independent semantic/proof review of the statements, but no need was found to reinterpret the checker as certifying topology, analytic KMS, exceptional classification, or the submitted standalone intake unchanged. Its count and axiom checks do not establish those meanings.

The verification paragraph's “all declarations originating in the new modules, including generated declarations” describes the intended environment enumeration correctly, subject to confirming the actual per-module roster and visibility in this Lean version. Do not strengthen it to “all declarations of the entire import closure were independently kernel-replayed and axiom-audited.”

## 7. Parent acceptance checklist / unavailable checks

1. Preserve the exact head/base/merge/tree bindings above. Do not build against current unrelated working-tree owners in place of this PR's source closure.
2. Independently compile/replay the exact source closure as already assigned to the parent, with current repository lock/process/cache protections. This reviewer has run none of those commands.
3. Obtain `audit.log`, `status.json`, copied source hashes, and `lean-version.txt` from artifact `12552794453`, or produce an independent source-bound replacement receipt. Verify actual total 73 and per-module declaration roster rather than relying on the summary.
4. Report actual warnings separately from errors/axiom failures. Do not infer zero warnings from job success.
5. Treat F1 as a concrete CI coverage improvement. F2–F5 are primarily hardening/scope qualifications unless independent execution exposes an actual omission or mismatch.
6. Keep any broader root build, strict full-closure audit, semantic/proxy screening, and repository-wide CI disposition separate from this scoped run.

No tests, builds, compilers, gates, checker imports/execution, existing-file edits, dependency changes, branch operations, merges, or comments were performed. Network access was limited to public read-only source/API requests; unavailable content was not bypassed. Only this new sandbox report is authored by the review and is staged immediately after waiting for the index lock, without a commit.
