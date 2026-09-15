# Madelung differential identities

## Proven scope

`lean/InfoGeometry/Algebra/MadelungDerivation.lean` uses Mathlib's
`Derivation Base Carrier Carrier`, not a replacement derivation class or an
assumed kinetic-energy derivative. On a commutative differential field it proves

\[
u=\frac{\partial a}{a},\qquad
\frac{\partial^2a}{a}=\partial u+u^2,
\qquad
\frac{\partial^2a}{a}
=\frac12\partial\left(\frac{\partial(a^2)}{a^2}\right)
+\frac14\left(\frac{\partial(a^2)}{a^2}\right)^2.
\]

The curvature statements require a nonzero amplitude. The half/quarter formulas
require characteristic zero. A logarithmic primitive is an explicit hypothesis
in the abstract field: arbitrary fields do not carry an analytic logarithm.

`MadelungLogDensityCalculus.lean` supplies the actual real-calculus counterpart.
For a globally positive differentiable density whose logarithmic derivative is
differentiable at the evaluation point, it proves

\[
\frac{(\sqrt\rho)''}{\sqrt\rho}
=\frac12(\log\rho)''+\frac14((\log\rho)')^2.
\]

Both derivatives are native `deriv`; the exponential amplitude's first and
second derivatives are proved, not stipulated. These are one-dimensional
identities, not a construction of a Laplace--Beltrami operator.

## Dynamics and signs

The phase equation is an explicit dynamical assumption. If spatial and temporal
derivations commute, differentiating

\[
\partial_t S+\tfrac12(\partial S)^2+P=0
\]

gives the proved Euler residual

\[
\partial_t v+v\partial v+\partial P=0,\qquad v=\partial S.
\]

`quantum_euler` specializes to
\(P=-c\,\partial^2a/a\) with \(\partial c=0\), fixing the force sign explicitly.
The amplitude transport equation also implies the density continuity equation
for \(\rho=a^2\). Neither dynamical equation is asserted to follow from the
curvature identity alone.

## Dependency order

`MadelungProofDependency.lean` defines a finite native `PartialOrder`:

```text
logDensity → osmoticScore → curvatureIdentity → hamiltonJacobi → eulerEquation
commutingDerivations ─────────────────────────────────────────→ eulerEquation
```

It proves that curvature and commuting derivations are incomparable prerequisites.
The order records this chosen proof decomposition; it is not a physical causal law.

## Boundaries

No Arnold diffeomorphism group, geodesic equation on such a group,
parahyperkähler manifold, chiral liquid, or pilot-wave interpretation is proved.
No inner product, Hilbert adjoint, or replacement for the existing Krein and
operatorial Madelung owners is introduced. The scalar differential identities
are explicitly scoped algebraic/calculus lemmas, not an operator-state model.
The pointwise squared logarithmic score is not itself an integrated Fisher
information theorem.

The earlier annealed-Weiszfeld descent request is separate and remains pending;
these files do not prove it.

## Validation

The earlier isolated check used Lean 4.28.0 and the Mathlib revision matching
the root manifest. The three production modules and their regression module
passed that check, but it is not acceptance under the required Lean 4.28.1.
Dependencies are now being rebuilt from pinned sources with 4.28.1; this
Madelung group still needs its own 4.28.1 rerun. No pinned-toolchain or
whole-repository success is claimed for these files. Regression examples cover exponential and Gaussian
log-densities, including negative Gaussian amplitude curvature. Nine printed
axiom audits contain only standard Lean axioms and no `sorryAx`.
