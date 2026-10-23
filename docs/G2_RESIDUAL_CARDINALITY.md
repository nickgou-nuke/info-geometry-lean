# Corrected residual cardinalities

Contract: for every native `WeylG2` parameter `p`, prove
`Nat.card (residualSubgroup p) = 2 ^ correctedLength p`.

Owners: `G2BruhatResidual.residualSubgroup` defines the intersection with
the conjugate by `w0 * weylNF p.1 p.2`;
`G2BruhatCellIntersectionCard.concreteBruhatCell_card_mul_intersection_card`
gives the orbit–stabilizer product 4096; and
`G2CellwiseCoordinates.weyl_cell_card` gives cell cardinality
`64 * 2 ^ correctedLength p`.

The native half-turn changes `(k,b)` to `(k+3,b)`. Its corrected lengths
are complementary. This replaces the legacy length formula that predicts
8 instead of 32 at `(2,true)`. No root-word parametrization is asserted.

Independent source review: Poincare accepted the native half-turn convention,
the intersection orientation, the positive cancellation step, and the scope.
The proof does not assume a residual-coordinate equivalence or its cardinality.

Parent verification passed: the owner build completed with exit 0 (9091 jobs),
and `G2CorrectedResidualCardAudit` completed with exit 0 (9092 jobs).
Logs: `/tmp/g2-corrected-residual-card.log` and
`/tmp/g2-corrected-residual-card-audit.log`.
All three theorem reports use exactly `propext`, `Classical.choice`, and
`Quot.sound`. The two new Lean modules emitted no warnings; imported owners
still emit warnings. The scoped staged diff check passed.

Independent QA (Popper) passed: session 31585 exited 0, 9092 jobs, shared
lock released. Log: `/tmp/g2-corrected-residual-card-qa.log`. All three
axiom reports again contain exactly the standard foundational axioms above.
There were 79 warnings (0 new-source, 77 dependency-source, 2 package).
Strict screening found 0 traps; scoped staged/worktree diff checks passed,
with no placeholders, authored axioms, or `native_decide`.

Status: accepted with limited scope, namely the all-parameter cardinality
theorem. Root-word coordinates and the repository-wide repair goal remain open.
