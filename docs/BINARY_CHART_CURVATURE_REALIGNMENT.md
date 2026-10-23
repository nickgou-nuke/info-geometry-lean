# Binary barrier chart: positive replacement

`BinaryBarrierCoordinateHessian.transformed_barrier_self_concordance_counterexample`
uses the actual interval barrier along `trajectory 1 0` and proves that its
standard squared self-concordance inequality fails at a specified point.
The affine-coordinate barrier remains self-concordant (`BinaryBarrierSurprisal`);
this property is not invariant under the nonlinear chart.

The constructive replacement retains the same potential and chart:

* Globally, the absolute third derivative is strictly less than twice the
  second derivative.
* The standard squared inequality holds at a chart point exactly when
  `1 ≤ 12p(1-p)`, with `p = trajectory 1 0 ξ`.

The proof uses the owner's actual iterated-derivative theorems, interval
membership, and a positive polynomial factor. It does not assume a bound or
introduce a substitute potential. The CAS script checks only the polynomial
readouts; native Lean checks the derivative-level statements.

Source discovery inspected `BinaryBarrierCoordinateHessian`,
`BipolarLogitBarrierDuality`, the `BinaryBarrierSurprisal` theorem surface, and
the `DikinApolloniusTrap` consumer's explicit warning about the nonlinear chart.
The new module is included by the existing coordinate-Hessian audit.
This resolves the local overstrong bound, not any claimed global matrix
self-concordance or physical interpretation. Independent semantic audit and
QA remain pending.

Verification: the locked `InfoGeometry.Convex.BinaryBarrierCoordinateHessianAudit`
build passed (8979 jobs). Both new declarations report only `propext`,
`Classical.choice`, and `Quot.sound`; the new module has no warnings.
The exact symbolic cross-check passed, OpenGauss screening found zero traps,
and the semantic-vacuity scan found zero findings. These are local results,
not a completion claim for the repository-wide goal.
