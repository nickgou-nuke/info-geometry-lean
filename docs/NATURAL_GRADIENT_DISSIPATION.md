# Natural-gradient dissipation: derivatives, rates, and limits

## Source ownership

The implementation reuses `InfoGeometry.Convex.HessianGeometry1D`, including
its actual derivative-based dual coordinate, Hessian metric, and Bregman
divergence. It does not introduce a competing `EpistemicPotential` structure
or define an algebraic product and label it a time derivative.

The owners are:

- `lean/InfoGeometry/Epistemology/NaturalGradientDissipation.lean`
- `lean/InfoGeometry/Epistemology/QuadraticNaturalGradientFlow.lean`
- `lean/InfoGeometry/Epistemology/NaturalGradientDissipationTests.lean`

The existing Bernoulli `EpistemicGradientFlow.lean` is preserved unchanged.

## General theorem

For a differentiable potential \(\psi\), write

\[
 B(x,y)=\psi(x)-\psi(y)-\psi'(y)(x-y),\quad
 v(x,y)=-\frac{\psi'(x)-\psi'(y)}{\psi''(x)},\quad
 I(x,y)=\frac{(\psi'(x)-\psi'(y))^2}{\psi''(x)}.
\]

For a trajectory satisfying the actual `HasDerivAt` equation
\(x'(t)=v(x(t),y)\), `hasDerivAt_divergence_along_flow` proves

\[
 \frac{d}{dt}B(x(t),y)=-I(x(t),y).
\]

Differentiability of the potential is required at the trajectory point. With
a positive Hessian there, `dissipation_nonneg` proves \(I\geq0\), and
`divergence_antitone` proves monotonicity along a globally defined flow.

Under the additional, explicitly supplied bound
\(\lambda B(x(t),y)\leq I(x(t),y)\), the integrating-factor argument in
`divergence_exponential_bound` proves, for \(t\geq0\),

\[
 B(x(t),y)\leq B(x(0),y)e^{-\lambda t}.
\]

This is an integrated estimate, not merely a renamed differential inequality.
`divergence_tendsto_zero` additionally requires \(\lambda>0\) and
nonnegative divergence along the trajectory, and proves convergence to zero
using native filters. The general theorems assume a globally defined,
differentiable trajectory; they do not prove existence for every potential.

## Explicit witness and finite-time boundary

The quadratic model reuses `Canonical.LieFenchelQuadratic.psi` on the real
line. Its derivatives and trajectory are proved, not supplied as fields:

\[
 \psi(x)=\tfrac12x^2,\quad g(x)=1,\quad
 B(x,y)=\tfrac12(x-y)^2,\quad I(x,y)=2B(x,y),
 \qquad x(t)=y+(x_0-y)e^{-t}.
\]

The module proves the exact decay identity
\(B(x(t),y)=B(x_0,y)e^{-2t}\), convergence \(x(t)\to y\), and
\(x(t)\ne y\) at every finite real time when \(x_0\ne y\).
The tests instantiate the general chain-rule, integrated-bound, and
convergence theorems on this model. Thus the hypotheses have a nonconstant,
verified witness, and exponential decay is not described as instantaneous
arrival.

## Dependency branches

```text
potential derivative + Bregman formula -> divergence derivative
divergence derivative + trajectory ODE -> dissipation identity
dissipation identity + positive metric -> monotonicity
dissipation identity + domination      -> integrated exponential bound
bound + positive rate + nonnegativity  -> divergence tends to zero
quadratic potential                   -> explicit trajectory and exact decay
explicit trajectory                   -> no finite-time arrival off target
```

The rate estimate uses the domination inequality directly, so it does not
depend on a separate proof of monotonicity. A positive metric alone is not
asserted to provide a uniform rate constant.

## What is not proved

`dissipation` is the squared gradient norm in the inverse Hessian metric.
No identification with a measure-theoretic Fisher information functional or
with the heat-flow de Bruijn identity is asserted. The domination hypothesis
is not presented as a proved logarithmic Sobolev inequality or as equivalent
to strong convexity. A general Bregman divergence is not automatically a KL
divergence of probability measures.

These results give no Dirac concentration theorem, zero-temperature limit,
QED correlation identity, Wick-factorization theorem, detector calibration,
or claim about cognition. In particular, the distinct formal result in
`DiracRelativeEntropyBoundary.lean` makes forward KL to a Dirac target infinite
whenever the source measure has nonzero mass outside that target.

No publication claiming these stronger conclusions is generated from this
module. A theorem export would have to preserve hypotheses and distinguish
these formal statements from physical modeling assumptions.

## Verification scope

The regression file passed with Lean 4.28.0, cached Mathlib, and isolated
outputs under the shared build lock: five examples and axiom reports for all
seventeen new theorems. The pinned 4.28.1 compiler is now installed, but a
separate import probe fails on an incompatible header in the existing
4.28.0 Mathlib `.olean` cache. A pinned-toolchain build is not claimed.
