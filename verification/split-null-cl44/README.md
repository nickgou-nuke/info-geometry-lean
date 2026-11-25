# Canonical null incidence and real Clifford operators

This focused check selects four source owners:

| Owner | Scope |
|---|---|
| `Lie.CanonicalZornRegularTrace` | Polarized conjugate contraction and actual operator trace |
| `Lie.CanonicalZornNullIncidence` | Conjugate image equals kernel, native kernel projection, rank and nullity four for arbitrary nonzero null elements |
| `Clifford.Cl44BornReciprocity` | Four-negative-generator involution and normalized Witt exchange in the native Clifford algebra |
| `Canonical.ZornCl44DiracTransport` | Quadratic isometry, representation on the actual real doubled Zorn carrier, transported CAR, Born action, and volume grading |

Every module has prefix `InfoGeometry.`. Read the
[intake contract](../../docs/SPLIT_NULL_CL44_INTAKE_CONTRACT.md) for hypotheses,
normalizations, the submitted table's counterexamples, and interpretation
boundaries. Read [SOURCE_REVIEW.md](SOURCE_REVIEW.md) for the distinction between
source review and native acceptance.

## Reproduction

From an ordinary independent checkout at the repository's exact pins:

```bash
python3 -B verification/real-matrix-split/check.py exe cache get
python3 -B verification/split-null-cl44/check.py
```

The wrapper uses the existing `verification/real-matrix-split` package and
the shared `verification/zorn-souriau/check.py` transaction. It retains that
transaction's original Zorn/Souriau default targets and all acceptance checks.
No dependency pin, toolchain, Lake cache, or existing theorem gate is changed.

An optional `--packages /absolute/packages.json` uses Lake's official package
location override format. The driver verifies all nine actual clean dependency
checkouts against the exact root and focused manifests before and after the
locked transaction. Linked worktrees and symlinked Lake roots are rejected.

The transaction:

1. Takes the maintained shared build lock and records the source revision.
2. Builds all four owners through native Lake.
3. Freshly elaborates each selected source with warnings treated as errors.
4. Enumerates module-owned declarations from the native environment, including
   private and generated declarations, and audits their transitive axioms.
5. Checks fifteen explicit reused declarations and verifies unchanged source,
   audit-source, package, override, and revision fingerprints.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted foundational
axioms. An error, warning failure, missing declaration, unexpected axiom,
untracked required evidence file, or changed fingerprint fails acceptance.

The hosted workflow checks the exact PR head without checkout credentials,
hydrates artifacts at the pinned revisions, and uploads available logs and
the receipt even on failure. Cache saving is limited to a successful manual
workflow run, as in the existing transaction workflow.

A successful focused run certifies these owners and their imported proof
dependencies at that revision. It does not certify every repository module,
the ordinary root path-package workspace, a projective incidence variety,
an algebra isomorphism to all real sixteen-by-sixteen matrices, or physical
Born-reciprocal dynamics.
