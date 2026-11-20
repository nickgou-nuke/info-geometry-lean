# Focused statistical geometry boundary check

Run from the repository root with the pinned Lean toolchain on `PATH`:

```bash
python3 verification/statistical-geometry-boundaries/check.py
```

The checker follows the maintained isolated-Mathlib pattern in
`scripts/quality/check-rectangular-peirce.sh`, uses `tools.build_lock`, and rejects
linked worktrees or symlinked `.lake` / `.lake/packages` directories. It verifies the unchanged root
and Mathlib pins, checks clean pinned Mathlib dependencies, resolves the native
compiler through Mathlib's Lake environment, and builds every repository module
in the audit's local import closure into a fresh directory.

The declaration audit checks all declarations belonging to the three new
mathematical owners and their reused dual-connection owner. Private and generated
constants are included. Only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` dependencies are allowed. Required endpoint names must also exist.

Each run writes module logs and a JSON receipt under
`.artifacts/statistical-geometry-boundaries/check-*/`. A successful run records
source and infrastructure hashes, compiler versions, exact dependency revisions,
owner counts, and an unchanged-source check.

This checks only the stated closure. It does not verify the whole repository,
its root Lake configuration, or the pre-push gate. See the
[theorem contract](../../docs/STATISTICAL_GEOMETRY_BOUNDARIES_CONTRACT.md) for the
mathematical scope and the separate root-package blocker.

## Recorded native result

The [observed result](observed-results.json) records a successful fresh run with
Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
All five modules in the local closure compiled: the three new mathematical
owners, the reused dual-connection owner, and the audit. The declaration audit
checked 99 declarations across the four mathematical owners, including 74
theorems (with generated declarations included), and required 14 named
endpoints. Only `propext`, `Classical.choice`, and `Quot.sound` occurred.

The JSON contains exact source, verifier, and pin hashes. It records the
baseline revision plus those checked contents; it is not a claim that the
entire baseline repository, all import consumers, or the root entrypoint built.
The new core retains one non-blocking `unnecessarySimpa` style warning in its
one-dimensional example.

## Repository gate result

The installed pre-commit hook passed during the local commit. The tracked
pre-push hook was then invoked locally for the proposed new branch, at commit
`ab9f669b25a88e66f1466eaddb54326624b2adf6`. Its incremental axiom/debt,
semantic-content, and source-scope audits all passed for the five changed Lean
files. Its Lake build exited 1 because the configured `HomotopyHypothesis`
package directory `external_refs/homotopy-hypothesis-lean4` is missing. The
pre-push hook therefore exited 1 before reaching its full root-package stage.
That invocation made no remote write.

The subsequent documentation update records this outcome; it does not change
the checked Lean sources, verifier, dependencies, or gate code. The focused
proof result is successful, while the root-package and publication gate remain
uncertified. Any draft publication must disclose that distinction.
