# Simultaneous self-adjointness of the Drazin shells

The native oblique example in `DrazinShellConsequenceExamples` has a
non-self-adjoint zeroth dressed shell. `DrazinShellSelfAdjointCriterion`
classifies exactly when this obstruction is absent from the whole family.

For a supplied Drazin inverse of index k and the existing `PowerMPFamily`
of the fitting nilpotent part, all shells with index below k are self-adjoint
if and only if the complementary projection is self-adjoint. Equivalently,
all shells at every natural index are self-adjoint. Negation gives a finite
bad-shell witness whenever the complementary projection is not self-adjoint.

Necessity uses the existing exact finite shell sum; sufficiency reuses the
existing shell self-adjointness theorem. No new shell, inverse predicate,
matrix carrier, or minimum-index hypothesis is introduced. The result does
not characterize an individual shell or assert existence of an MP family.
The zero-index case is covered by the same finite-sum theorem.

Parent session 42077 passed (3,182 jobs, exit 0), with zero own warnings,
log `/tmp/drazin-shell-selfadjoint.log`. Semantic review passed, strict
screening found zero traps, and scoped staged diffs are clean. The companion
audit requests four axiom reports and preserves the native oblique negative
example in two API checks. Independent QA session 8153 passed together with the vacuum audit (3,228
jobs, exit 0), including this module's four axiom reports and two examples.
Zero own warnings; standard axioms only. Log: /tmp/witt-drazin-final-qa.log.
Final semantic A-A review confirmed the source scope. Accepted.
