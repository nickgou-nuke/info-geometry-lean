# Validation status: Klein operator hierarchy

**Status: source-reviewed draft; native Lean elaboration and axiom auditing
have not run for the new owners.**

The four Lean owners have complete proposed proof terms and independent
source review. They must not be reported as kernel-verified. The previous
Zorn/Souriau draft's pending validation is not discharged by this extension.

## Native attempt actually observed

At 12:43 Europe/Sofia on 2026-11-24, from the independent checkout
`/tmp/info-geometry-zorn-primal-dual-20261124`:

```bash
python3 verification/zorn-primal-dual/check.py \
  --suite klein-operator-hierarchy \
  --lean /workspace/scratch/058543be00a5/lean-runtime/lean-4.34.1-linux/bin/lean \
  --packages /workspace/scratch/058543be00a5/info-geometry-lean/.lake/packages \
  --no-wait-for-build-lock --force
```

Observed process exit code: **2**.

The maintained exclusive lock was already held by the separate
`real-matrix-split:83` build. This invocation did not wait or begin Lean
elaboration or an axiom audit; its preflight did execute `lean --version`.
No other process or lock was killed, cleared, or bypassed.

The exact receipt is preserved in `blocked-native-check.json`:

| Field | Observed value |
| --- | --- |
| Run ID | `ee0a176fa88149a985efe2f8435dd7f6` |
| Status | `blocked` |
| Compiler command records | `[]` |
| Audit expected | `true` |
| Audit status | `not-run` |
| Started, UTC | `2026-11-24T10:43:12.761030+00:00` |
| Finished, UTC | `2026-11-24T10:43:13.021766+00:00` |

The preflight inspected native Lean 4.34.1, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`. Its executable SHA-256 was
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The eight actual dependency packages matched their pinned revisions with
clean tracked sources; Mathlib was
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

These are environment observations. They do not show that any new theorem
elaborated or that an imported artifact is a current proof certificate.

## Prepared validation surface

Read-only source traversal found a closure of **25 repository modules** for
the four Klein targets. This count is an import-graph observation, not a
compiled-module count.

The new audit targets every declaration owned by the four new modules and
the reused `Canonical.ZornCliffordRepresentation` owner, including private
and generated declarations. It follows transitive axiom dependencies and
allows only `propext`, `Classical.choice`, and `Quot.sound`. It rejects unsafe
or partial declarations and requires a nonempty declaration count per owner.
**That audit has not executed.**

| Validation source | SHA-256 at the blocked attempt |
| --- | --- |
| `verification/zorn-primal-dual/check.py` | `293bd44367d8594ae9f51d8f9a148ca90e8a28cc8fa61e112aa3e5658a7a2ca5` |
| `verification/klein-operator-hierarchy/Audit.lean` | `db2f5841066eada24f0bac3900e73db41f20660c5d99ff4542ce02856d06bf5b` |

The checker retains the original Zorn/Souriau suite as its default and adds
a separately selected Klein suite. Reports distinguish a full-suite audit
from a custom target selection. Source review also repaired a child-process
cleanup issue: an interrupted driver now reaps only its own native compiler
child before releasing its lock. No lifecycle test has been executed here.
The maintained hook/gate sources and dependency pins were not changed.

## Source review and scope

`SOURCE_REVIEW.md` records the independently reviewed hashes of the first
three owners, their exact hypotheses, and the two repaired Mathlib API calls.
`VOLUME_REVIEW.md` separately reviews the fourth owner and its orientation
sign. The integrated owner bytes match those reviewed snapshots.

`QA_REVIEW.md` separately records independent inspection of the final checker,
audit, four source hashes, dependency metadata, and blocked receipt. That
reviewer did not run native elaboration, tests, gates, or the axiom audit.

The review is bounded. It does not certify the whole transitive import graph,
the public umbrella, all existing repository theorems, or a group-level
classification. The exact full Clifford isomorphism, exterior grade-eight
identification, smooth gauge fields, and cotangent symplectic groupoid remain
outside the implemented scope.

## Required follow-through

When the shared build lane becomes available, rerun the command above
(omit `--no-wait-for-build-lock` to wait). Resolve any actual native
elaboration or linter errors, rereview changed proof terms, and execute the
declaration audit. Run the original Zorn/Souriau suite separately to discharge
its earlier validation debt.

The repository's staged proof gate, pre-push gate, public umbrella, and full
root build are separate checks. No passing result for those checks is claimed
in this continuation. The published pull request remains a draft candidate.
