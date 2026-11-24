# Independent verification-runner source review

Date: 2026-11-24. Reviewed the current local changes in
`/tmp/info-geometry-zorn-primal-dual-20261124` after integration of the genuine
Witt/Born owner, conjugate-range exactness addition, and verification-only raw
table counterexamples.

This reviewer ran no Lean compiler, Lake build, native test, or axiom audit.
The review used source reads, Git diffs, content hashes, and an independent
read-only AST/import inventory. The root's native receipts determine runtime
outcomes separately.

## Reviewed files

| File | SHA-256 |
| --- | --- |
| `verification/zorn-primal-dual/check.py` | `801c1ccf518eb511a24896ec16853e00d9edfa323a5d3d30b4ac33ecfca44c2e` |
| `verification/supplied-zorn-counterexample/Audit.lean` | `bf991df99cf2429ad16d207224c344fed324eb902160450c1bb5c3f0a5ffa57c` |
| `verification/witt-born-null-exactness/Audit.lean` | `6a7bc6bf3595b5cc29f38b8515f082c463ec7d3756f67f8f8dfbbc19068e5d30` |
| `lean/InfoGeometry/Canonical/ZornCliffordWittBorn.lean` | `cc252e95448fb4e51f13fbe8cebc2d2ea55aa28f6ed3bc58979859f94d2ca0ce` |
| `lean/InfoGeometry/Verification/SuppliedTableCounterexample.lean` | `21a3b723a83bdd4904e78369dd2879870a4edd5470b240fb6f72f5c6b2c1d9b0` |

The root corrected the counterexample candidate's nonexistent import
`Mathlib.Data.Matrix.Notation` to the pinned
`Mathlib.Data.Fin.VecNotation`; the source uses vector literals, not matrices.
The production Born owner matches the previously reviewed candidate bytes.
The exactness insertion matches the previously reviewed two-theorem addition.

## Shared build lock

The maintained helper `acquire_build_lock` calls `.acquire()` before returning
its `BuildLock`. Using that helper directly as a context expression causes
`__enter__` to acquire again, incrementing the internal reference count to two;
one `__exit__` release then leaves it at one.

The checker now constructs
`BuildLock(DEFAULT_BUILD_LOCK_PATH, ..., block=args.wait, shared=False)`
directly in the `with` statement. That gives one acquisition and one release,
while preserving the maintained lock path, exclusive mode, metadata, and
nonblocking busy result. The shared lock implementation itself is unchanged.

The existing child cleanup and inherited lock descriptor remain in place.
The root owns all runtime validation; this review does not claim a lock
lifecycle test.

## Suite and audit coverage

The new light suite contains only
`InfoGeometry.Verification.SuppliedTableCounterexample`. Its audit imports
that owner, requires a nonzero owned-declaration count, rejects unsafe and
partial declarations, and collects transitive axiom dependencies.

The full `witt-born-null-exactness` suite combines both earlier target sets,
the actual new Born owner, and the counterexample owner. Independent static
inventory found:

- 11 explicit top-level targets;
- 50 repository modules in their import closure;
- 15 audited owners, all present in that closure;
- 12 task-owned modules compiled with warnings as errors, all included in
  the full audit;
- no public, private, multi-module, indented, or otherwise noncanonical
  import lines in this closure that the checker's current import expression
  would miss.

The full audit preserves the earlier groupoid instance check and all owners
selected by the two previous audits. Both new audits permit only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

The counterexample owner is deliberately absent from `InfoGeometry.All`;
only the genuine Born owner is added to the production aggregate imports.

## Scope and result

The checker changes only target/suite selection, task-owned warning coverage,
and correct acquisition of the maintained lock. Compiler pins, dependency
pins, cache policies, and maintained staged/push gates are unchanged.
The verifier's own content hash remains part of its environment fingerprint,
so changing this checker invalidates reuse of a previous fingerprint.

No source-level coverage, lock-ownership, or axiom-policy defect was found in
the reviewed diff. This is source review, not a successful native run.
A passing light counterexample suite would establish only those exact
counterexamples and that owner's axiom footprint. It would not establish
compilation of the genuine-Zorn additions or the full PR.
