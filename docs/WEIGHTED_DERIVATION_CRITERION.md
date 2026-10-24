# Left-weighted derivations: exact replacement contract

The existing `QuantumGeometry/BerryKeatingDilationBridge` defines `opEuler K D x`
as `K*D x` and computes its Leibniz defect `(K*x-x*K)*D y`. Its
`complexDerivationEquivOpDerivation` identifies its function-field derivations
with the existing noncommutative `ExteriorAlgebra.OpDerivation`.

The extension works on that native owner for any commutative scalar ring and
associative algebra: weighting preserves the Leibniz law iff all commutators
of the weight annihilate the image of D. If `D y*z=1`, this is equivalent to
centrality of the weight. It also constructs the weighted derivation using
the exact criterion, with no new carrier or stronger ambient commutativity.

Source searches covered `opEuler`, `leibniz_defect`, `OpDerivation`, weighted
derivation and centrality statements and their maintained consumers. The
existing five-grading owner supplies real inner derivations for the matrix
audit. No spectral or analytic Berry–Keating claims are asserted.

`QuantumGeometry/EulerDerivationCriterion` specializes the criterion through
the existing equivalence: under `D K=1`, the Euler operator satisfies Leibniz
iff `K` commutes with every element. The audit reuses the existing inner
derivation on `Matrix (Fin 2) (Fin 2) ℝ`, proves a noncommutativity witness,
and checks a right-invertible value, identity-weight success, and failure for
a noncentral diagonal weight.

Final parent locked build session 44590 exited 0 (8932 jobs), log
`/tmp/weighted-derivation-audit.log`. Independent QA session 80708 exited 0
(8932 jobs), log `/tmp/weighted-derivation-qa.log`. Six axiom reports and three
examples passed. The union is exactly `propext`, `Classical.choice`,
`Quot.sound`; zero own-source warnings, eight dependency warnings and two
package notices. Strict screening found zero traps; scoped diff checks passed.
Independent contract and final-source mathematical reviews passed.
