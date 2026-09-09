# Binary simplex extension: mathematical scope

This is a reconstruction of a possible mathematical argument, not recovery
of the author's private reasoning or validation of a spectrometry model.
Its intended presentation use is optional mathematical backup material.

## Repository search and reuse

Searched owner filenames and declaration bodies in `lean/InfoGeometry` and
`proofs`, then ran `tools/infra/context_preflight.py` with external context.
The six TCS-specific module names asserted in the draft were not found.
Existing owners inspected:

- `Probability/SquareRootSimplexBridge.lean`: finite square-root embedding,
  sphere normalization, inverse, and Fisher quadratic form. Its amplitude
  convention is **2 sqrt(p)**, giving radius two, not radius one.
- `Analysis/BipolarCayleyOccupation.lean`: logistic/log-odds equivalence
  and the hyperbolic tangent relation. Imported and reused directly.
- `ExponentialFamily/Bernoulli.lean`: Hessian of the log partition in the
  natural parameter. Its coefficient p(1-p) must not be confused with
  the reciprocal coefficient in probability coordinates.

## Reconstructed mathematical chain

1. Begin with a binary distribution (p,1-p). Its weighted variance is
   p(1-p); its nonnegative square-root coordinates lie on a circle.
2. A product of two binary distributions gives four normalized amplitude
   coordinates. For events, product probabilities require independence.
   Complementary events are disjoint, so their intersection has probability
   zero even though p(1-p) is strictly positive in the open simplex.
3. The observation Cx-Bx², under x=(C/B)p, equals (C²/B)p(1-p).
   Prove its actual derivative, vertex bound, reflection symmetry and
   noninjectivity. A zero derivative is loss of local sensitivity of this
   observation, not a singularity of the simplex itself.
4. Reuse the logistic chart at 2ξ to obtain the profile
   C²/(4B) (1-tanh² ξ). No evolution equation follows from this substitution.
5. Distinguish Fisher 1/[p(1-p)] from log-odds 1/[p²(1-p)²].
   The latter is proved to be the squared derivative of log p-log(1-p).
   The coefficients are strictly unequal on the whole open interval.
6. The field V(p)=2vp(1-p) satisfies V'V+ΓV²=0 with
   Γ=(2p-1)/[p(1-p)], and its log-odds kinetic energy is 2v².
   The field identity extends algebraically to the endpoints under Lean's
   totalized division; the geometric interpretation does not.
7. Radial inversion is involutive away from zero and maps the exterior
   radial interval to probabilities in (0,1]. This interval is not compact;
   adding its missing endpoint is a separate construction.
8. The rational dead-time residual and exponential lower bound are exact
   inequalities of functions. They do not identify dead time with TCS.

## Physical interpretation boundaries

The scale defect is ordinary failure of degree-one homogeneity. The proofs
do not establish a quantum anomaly, dimensional transmutation, negative
physical mass, Andreev reflection, or conversion of a detector into 4π
coverage. A square-root probability carries no recoverable quantum phase.
Total summing-out losses and photopeak summing-in generally have different
coefficients. Geometry variation and activity variation are distinct.

## Verification and remaining development frontier

`Probability/SimplexQuadraticResponse.lean` contains direct proofs, with no
custom axioms or proof placeholders. Its audit module prints dependencies
of every theorem. Reproduce with the shared locked-build runner and targets
`InfoGeometry.Probability.SimplexQuadraticResponse` and
`InfoGeometry.Probability.SimplexQuadraticResponseAudit`.

This is a scoped extension, not completion of every claim in the draft.
Still to develop: a bundled smooth/Riemannian interpretation of the metric
and connection; an explicit time-parameterized trajectory and Hamilton–Jacobi
primitive; the absorption integral and its centroid bounds; asymptotic
cubic remainder estimates; and any measure-theoretic detector experiment.
These require actual theorems, not additional physical assumptions.
The repository-wide build and independent review remain separate checks.
No numerical experimental values or slide claims are promoted by this work.

## Subsequent search and verified extension

The frontier list above is superseded in part by deeper inspection of the
shared checkout. `Analysis/LogOddsSimplexGeometry.lean` contains the explicit
trajectory, its first and second derivatives, the metric connection and
stationary Hamilton–Jacobi theorem. Repairs appeared in that shared owner
during this side conversation; its dependency build now passes. The side
conversation did not overwrite those concurrent repairs.

`Probability/BinaryAitchisonLogOdds.lean` adds the remaining bridge using
the existing `AitchisonFinite` and `LogOddsSimplexGeometry` definitions:

- CLR(p,1-p) = (logit(p)/2, -logit(p)/2).
- The binary Aitchison inner product is logit(p) logit(q)/2.
- Squared CLR distance is (logit(p)-logit(q))²/2.
- The squared coordinate speed gives half the existing log-odds metric.
- The existing logistic trajectory becomes an affine CLR line.
- W(p)-2v²t satisfies the time-dependent Hamilton–Jacobi equation using
  actual derivatives and the existing Hamiltonian.

This removes the trajectory and Hamilton–Jacobi primitive from the missing
list. A bundled manifold/connection construction and the physical absorption
integral remain separate work. The six new declarations have an explicit
`BinaryAitchisonLogOddsAudit` target; scoped verification does not constitute
a repository-wide release or an independent semantic review.

## Barrier coordinate correction

Deeper search found `Convex/BipolarLogitBarrierDuality.lean`, which already
proves genuine derivatives of the interval barrier and separates it from
the odd logit coordinate. `Convex/BinaryBarrierCoordinateHessian.lean`
reuses that owner and the logistic trajectory to prove nine further results.
Writing p = logistic(2ξ) and F(p) = -log p-log(1-p):

- F(p(ξ)) = log(4)+2 log(cosh ξ).
- Its first three derivatives are 4p-2, 8p(1-p), and
  16p(1-p)(1-2p).
- The pulled-back original Hessian is 4[p²+(1-p)²].
- The transformed scalar Hessian minus that pullback is -4(2p-1)²,
  exactly the gradient-times-acceleration correction in the chain rule.
- At p=15/16, the transformed potential violates (F''')² ≤ 4(F'')³.
  It is therefore not globally standard self-concordant in ξ coordinates.

The old global self-concordance descriptions in the two log-cosh potential
modules have been corrected. No theorem equates these scalar Hessians with
an operator logarithm, and no modular-flow claim follows from this calculation.
