# Finite Fock chordal norm v2: parser repair

Candidate: FiniteFockChordalNorm20261024v2.lean.
Exact same nine declarations and norm claim as the updated frozen v1.
Diagnostic: /tmp/qa-a-fock-chordal-norm-z9bvnmad/compile.log.

The sole reported candidate error is line110: unexpected token |*.
Separate the closing absolute-value delimiter from multiplication:
`|s| * ‖x‖` in the final theorem statement. No proof body is changed.
The current native theorem name movingPolePlus_chordal_square_and_compression
is retained, and no duplicate commutator-square result is added.

Original native spinor carrier/local metric, derived symmetry, actual CAR,
and exact every-vector displacement norm are preserved. No new assumptions,
instances, budgets, builds/tests, or live-owner edits. V1 remains unchanged.
Independent AA and serialized QA are required; the parser failure does not
supply a completed kernel/axiom receipt for the final declaration.
