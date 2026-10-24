# Exact noncommutative chiral factorization

The existing `Canonical/OperatorChiralDeterminantDefect.lean` computes the
actual adjugate product on `Matrix (Fin 2) (Fin 2) A` and supplies sufficient
commutation conditions. The new `OperatorChiralFactorizationCriterion.lean`
classifies exactly when that product equals its scalar diagonal readout:

`Commute r p ∧ Commute l m ∧ [p,m] = [r,l]`.

The last equality allows two nonzero commutators to cancel. No determinant
on a noncommutative ring, centrality of the readout, or reverse-order
factorization is asserted. A second theorem specializes the criterion to
the existing associative `Physics.OperatorZornMatrix` carrier.

The audit checks a noncommuting cancellation family, an explicit integral
matrix noncommutation, and failure from an uncancelled diagonal commutator.
Bounded maintained owner/dependent searches located sufficient conditions
and exact defect formulas, but no equivalent iff in those results.

Independent semantic AA passed. Parent locked audit passed on 2026-10-24:
session 38884, `/tmp/chiral-factorization-audit.log`, 8,930 jobs, exit 0.
All three examples passed; all three axiom requests report only `propext`,
`Classical.choice`, and `Quot.sound`. There were no source warnings and two
existing package notices. Independent QA accepted the three-batch combined
audit: session 10916, `/tmp/chiral-bivector-graph-final-qa.log`, 8,941 jobs,
exit 0. Fourteen standard-axiom reports and nine examples passed across
the three audits; zero own-source warnings, five dependency warnings, two
package notices. Six-source strict screening found zero traps.
