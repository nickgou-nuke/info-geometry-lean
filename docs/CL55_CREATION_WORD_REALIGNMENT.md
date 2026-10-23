# Creation-word support and occupation grades

## Ground-truth contract

The carrier is the existing native real Clifford algebra `Cl55`, with the
five `creation55` generators and `creationWord` from
`Clifford/Cl55CreationWordGradeObstruction.lean`. This is not a matrix or
scalar replacement. In module `Cl55CARSpinAutomorphism`, declarations
`InfoGeometry.Clifford.Clifford55.creation55_sq` and
`InfoGeometry.Clifford.Clifford55.creation55_anticommutator` supply the
square-zero and exchange relations.
The existing owner proves `creationWord_ne_zero` under `List.Nodup`,
`creationWord_mem_grade` at the list length, and `grade_unique_of_ne_zero`.

The source-confirmed gap in that API is the converse support criterion:
a word vanishes exactly when its index list repeats a generator. The new
module proves left annihilation when a generator occurs in the word,
vanishing for non-Nodup lists, nonzero iff Nodup, and exact membership in
an occupation grade: either the word is zero, or the grade equals its length.
This completes the creation-word interpretation of the grade-five witness;
it does not identify occupation grading with contact grading or classify
all elements of the Clifford algebra. The existing Penrose Witt completion
was separately inspected and needs no duplicate composition construction.

## Verification

The parent locked build of `InfoGeometry.Clifford.Cl55CreationWordSupportAudit`
passed (8948 jobs), with four reports using only `propext`, `Classical.choice`,
and `Quot.sound`. Strict screening found zero traps and the scoped staged
diff check passed. Log: `/tmp/cl55-creation-support-build.log`.
Independent A-A Poincare passed the final three files after a declaration-name
correction in this contract. Independent QA-A Popper reran the locked build
(8948 jobs, exit zero), four standard axiom reports, strict screening and
scoped staged/worktree diff checks. All passed. Its log is
`/tmp/cl55-creation-support-qa.log`; it reported 42 dependency/package
warnings and none in the new files. Acceptance is limited to these
creation-word support and occupation-grade statements. The repository-wide
counterexample realignment remains open.
