# Two-coordinate skew maps: constructive classification

## Ground-truth contract

`Thermo/BipolarTwoDimensionalSkewObstruction` owns `State2`, the actual
two-coordinate real state space, its coordinate vectors and dual covectors.
Its `skew_operator_eq_zero_of_eta_casimir` proves that a skew map from the
dual to the state space killing the eta covector is zero. The existing
`BipolarGENERICThreeCoordinateModel` instead constructs a nonzero reversible
operator with this Casimir on a larger carrier. That construction is retained.

The implementation classifies skew maps on the original carrier using
native `LinearMap`: for a unique real coefficient c, the output on α is
`![c * α thetaBasis2, -c * α etaBasis2]`. The coefficient is obtained by
evaluating `etaCovector2 (L thetaCovector2)`. It then characterizes the
kernel of every member of this family. This is a classification of actual
linear operators on the existing finite state/dual spaces, not a scalar
substitute for an operator theorem or a claim about arbitrary dimensions.
The existing coordinate decomposition theorems and skew relation suffice;
no new assumed structure is introduced. No Poisson Jacobi or full GENERIC
construction in two dimensions with a nontrivial Casimir is asserted.

## Verification

The parent locked build of `InfoGeometry.Thermo.BipolarSkewClassificationAudit`
passed (8928 jobs). Its five axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`; no warnings came from the new files.
Log: `/tmp/bipolar-skew-build.log`. Independent A-A Poincare passed the
semantics and scope. Independent QA-A Popper returned
`ACCEPTED_WITH_LIMITED_SCOPE` after rerunning the locked build (8928 jobs,
exit zero), all five axiom reports, strict screening (zero traps), and
scoped staged/worktree diff checks. The QA log is `/tmp/bipolar-skew-qa.log`.
Only two package-local-change warnings were reported, with none in the new
sources. This is a verified classification on `State2`, not completion of
the repository-wide counterexample realignment.
