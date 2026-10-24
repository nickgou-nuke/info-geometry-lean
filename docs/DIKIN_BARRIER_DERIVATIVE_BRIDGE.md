# Dikin barrier derivative bridge

Contract: use the existing real functions `dikinScaleBarrier` and
`dikinScaleMetric` from `Quantum.DikinApolloniusTrap`. Identify the potential
with `intervalBarrier (trajectory 1 0 ξ) - log 4`, then prove its actual second
derivative is the defined metric. Transport the existing global generalized
curvature bound and exact standard squared self-concordance region.

Owners read: `Convex.BinaryBarrierCoordinateHessian` (nonlinear coordinate
defect and counterexample), `Convex.BinaryBarrierChartCurvature` (constructive
replacement), `Quantum.DikinApolloniusTrap` (potential and metric),
`Analysis.LogOddsSimplexGeometry` (actual logistic trajectory). Consumers
`Canonical.DikinApolloniusTrapCapstone` and
`Canonical.CantorBernoulliGrandCanonicalBoundary` currently use metric
positivity and the conditional contraction estimate. Their theorems remain
unchanged. Maintained Lean reference searches found no actual second-derivative
identification for `dikinScaleBarrier` in those references.

No global standard self-concordance, no automatic preservation of a Hessian
under nonlinear coordinate changes, and no proof that a specified
Blahut–Arimoto operator contracts is asserted. These are finite scalar barrier
statements on their existing owner carrier, not substitutes for operator or
colimit results.

Implemented six named lemmas in `Quantum.DikinBarrierDerivativeBridge`.
The function-level equality of first derivatives transports both higher-order
bounds; the metric identity uses the two independently computed first
derivatives to obtain `tanh ξ = 2p - 1`.

Parent locked audit session 25165 exited zero (8981 jobs), including three
examples: first derivative zero at equilibrium, second derivative two there,
and global strict positivity of the second derivative. Seven axiom reports
(six new results and the original counterexample) contain only the standard
foundational axioms. Independent semantic review passed, strict screen found
zero traps, and scoped diffs are clean. Independent final QA session 53169
exited zero (8981 jobs), confirming seven standard-axiom reports, three
examples, and zero own-source warnings. The 36 dependency-source warnings
and two package notices are outside these additions. Accepted with the scope
above. Session-local evidence: `/tmp/dikin-derivative-audit.log` and
`/tmp/dikin-derivative-qa.log`.
