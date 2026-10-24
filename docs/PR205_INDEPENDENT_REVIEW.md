# PR #205 — independent source and kernel review

## Decision

**The scoped algebraic contribution passes independent review and verification.**
No mathematical correctness blocker was found. Two nonblocking follow-ups are
listed below. This is not a merge, GitHub approval submission, full-repository
build verdict, or certification of the earlier geometric rhetoric.

Reviewed head: `ea08baa1649c9eeaf45638d6e7edef2f971ad1be`.
Base: `21189e55133ed207043f2f05e37aa52d1fc8a9f5` (`main`).
PR: <https://github.com/nickgou-nuke/info-geometry-lean/pull/205>.

The public GitHub API confirmed open/unmerged status, eight added files,
847 additions and zero deletions. All eight fetched files matched their Git
blob hashes. No patch was applied to the working tree; no branch was checked
out, dependency pin edited, remote comment posted, or merge performed.

## Findings

1. **CI coverage, nonblocking for the reviewed run** —
   `.github/workflows/peirce-weyl.yml:3–11` triggers only on the new owners,
   checker and workflow. Changes solely to imported repository owners,
   `tools/quality/check_reviewed_prs.py`, `lean-toolchain`, or
   `lake-manifest.json` do not trigger this workflow. Cover those dependencies
   conservatively (e.g. `lean/**` plus helper/pin paths), or install a
   dependency-aware trigger. Other workflows may provide independent coverage;
   this finding does not assert otherwise.
2. **Existing-owner reuse nit** — `Core/PeirceWeylUnits.lean:60–66`
   reproves the exact already-imported
   `InfoGeometry.Core.DiracSuperalgebra.majoranaMinus_sq h hd` theorem.
   Reuse that proof or its owner directly rather than maintain another
   expansion. This is not a false theorem.

Further optional checker hardening: require a positive audit count per target,
record per-module counts and warning totals, and distinguish fresh from reused
output directories. These are future robustness improvements, not evidence of
missed declarations or warnings in this head. Our independent replay checked
all five owners separately.

A suggested Jordan-reuse criticism was **withdrawn after version checking**:
`Core/JordanAssociatorRing.symm_operator_commutator` exists in the current
shared checkout but not in the PR's exact base. The PR correctly reuses the
base associator identity in `associator_orientation`. It must not be rejected
for failing to call an API absent from its stated base.

## Mathematical scope checked

- The actual existing four-equation Moore–Penrose predicate supplies the
  support laws, including inverse square-zero from the square-zero input.
- Harmonic completion gives a genuine two-sided ambient unit even when the
  active support is proper. Conjugation signs and the fourth-power law agree.
- Third/sixth-root equations use the active support as constant; exact order
  and ambient root-of-unity assertions are correctly withheld.
- Arbitrary central weights, including zero, give correctly oriented density
  and weighted cyclic-trace identities. No analytic KMS condition follows.
- The native Jordan endomorphism commutator is `[[s,t],x]`, with the
  unnormalized product and correct endomorphism-composition convention.
- Integral 2×2 and 3×3 witnesses check noncommutation, proper support, the
  grading/Phi2 distinction, opposite Jordan sign, and nonzero local associator.
- The master theorem stays on one carrier with an actual MP witness and an
  explicitly cyclic linear functional. It does not add an inverse-existence,
  positive-state, manifold, connection, Clifford-embedding, or exceptional
  Lie-algebra classification theorem.

Current unmerged/shared owners overlap with portions of this API. The reviewers
separated that future integration issue from reuse available in the PR base.
If those lines of work land together, consolidate the low-level ring facts
and verify the combined source tree; PR-only verification does not certify a
future combined tree.

## Independent verification performed by the parent

Exact source files were fetched by immutable head SHA into
`/tmp/pr205-review-ea08baa`. A comment-aware source-import traversal recovered
**five new modules plus sixteen repository dependencies**. Every dependency was
separately downloaded at the PR base and compared byte-for-byte: all unchanged.
All root dependency pin entries matched the local pinned manifest.

Compilation used the existing root dependency environment, with a fresh
isolated output library first in `LEAN_PATH` and the root repository owner
output directory excluded. All 21 repository modules were compiled from the
exact downloaded sources; current dirty owner sources were not substituted.
The shared build lock and compiler-process prechecks serialized verification.
No cache was deleted, no running build was killed, and no dependency update
command was run.

- Lean: **4.34.1**.
- Mathlib: **`d13f23b723b8a846827a245b89c10fc7d3f11612`**.
- All 21 source modules compiled successfully.
- All five new modules: **zero compiler warnings**.
- Text inventory: **31 named theorems, 12 definitions, 6 API checks**.
- Strict kernel replay/transitive axiom check: **73 declarations**, all PASS.
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- Source-aware forbidden-token check passed; final source hashes unchanged.

| New owner | Replayed declarations |
|---|---:|
| Core/PeirceWeylUnits | 39 |
| Core/PeirceDensityIntertwining | 9 |
| Core/JordanMultiplicationClosure | 12 |
| Canonical/PeirceWeylSynthesis | 1 |
| Canonical/PeirceWeylExamples | 12 |
| **Total, including generated declarations** | **73** |

The strict replay uses the repository's `tools/infra/axiom_check.lean`, not just
selected `#print axioms` commands. The sixteen dependencies were compiled but
were not each separately selected for all-declaration replay; their axioms
reachable from the new owners were checked transitively. Dependency warnings
remain and are recorded separately.

An initial environment-acquisition attempt from the Mathlib subdirectory
triggered Lake's ordinary nested dependency bootstrap and failed before any
new module compiled, because its diagnostic output was mixed with the path
readout. The successful second attempt used the established root environment
and separated stderr. This setup failure is not counted as a successful run;
no caches were removed to recover from it.

## External CI evidence and limits

Public API metadata confirms workflow **40077004618**, attempt 1, and job
**120822411313** completed successfully. The receipt reviewer verified identical
Git tree `895f1f864aa45b23aec57ccde1a30bc424b3fad0` for the head and reported
merge revision `01c872dd32ebd50cc8f72f09e32067df2de40caf`.

An unexpired verification artifact is listed with digest
`sha256:cfc8807ad8f68275194e7eb490e5d75cc99d5a17b85d015929a48ead1741923a`.
Artifact archive download required authentication (401); job-log download
returned 403. The supplied `sandbox:/mnt/data/...` attachments were not mounted
in this environment. Therefore the artifact ZIP digest, attachment contents,
and supplied additive-patch replay were **not independently reproduced** here.
Our local compile and 73-declaration replay independently establish the scoped
source verification without relying on those unavailable bytes.

## Preserved review artifacts

- `scratch/agent_sandbox/pr205_review_20261024/math/report.md`
- `scratch/agent_sandbox/pr205_review_20261024/receipts/report.md`
- `scratch/agent_sandbox/pr205_review_20261024/parent/status.json`
- `scratch/agent_sandbox/pr205_review_20261024/parent/source-closure.json`
- `scratch/agent_sandbox/pr205_review_20261024/parent/strict-replay.log`
- `scratch/agent_sandbox/pr205_review_20261024/parent/pr205_verify_exact.py`

The verifier script expects the immutable downloaded source snapshot described
by its source manifest; it is not a self-contained downloader. Detailed local
compile logs remain in `/tmp/pr205-independent-verification/`; successful
combined output is `/tmp/pr205-independent-verification-run2.log`.
Review artifacts are staged, not committed. The PR itself remains untouched.
