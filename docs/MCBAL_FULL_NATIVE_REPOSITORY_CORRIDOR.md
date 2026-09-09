# The full native repository corridor behind the mcbal comparison

## Correction of scope

The repository does not merely contain a finite softmax owner plus a prospective
spin-model mean-field module.  It already contains a broad, interconnected
architecture covering Sinkhorn scaling, Birkhoff geometry, primal/dual convex
optimization, weighted detailed balance, graph affinities, Hodge currents,
mass-spectrometric directed Gramians, modular Hessians, Information Bottleneck
iterations, finite Wasserstein envelopes, Bayesian projection, and Dikin
confinement.

The proper task is therefore not to invent these layers again.  It is to locate
the existing theorem owners and identify the one remaining direct bridge to the
mcbal vector-spin stochastic model.

This document distinguishes:

1. theorem-owned repository mathematics;
2. computational or external mcbal models; and
3. the still-missing intertwining theorem.

## 1. Gibbs routing is only the first layer

The local routing weights are already a finite Gibbs state.  The repository
proves positivity, normalization, the free-energy/KL identity, and variational
minimality.  `ThermodynamicSwitching` turns these weights into a token-to-expert
switch matrix.

The switch is always row stochastic.  When its column sums are also one, it lies
in the Birkhoff polytope.

## 2. Sinkhorn is diagonal Weyl gauge fixing

`Canonical/SinkhornFoundation.lean` does not treat Sinkhorn scaling as a black
box.  It proves that row and column normalization are respectively left and
right diagonal gauge transformations:

```text
rowNormalize(M) = diag(leftWeylScale(M)) * M,
colNormalize(M) = M * diag(rightWeylScale(M)).
```

Hence one row/column Sinkhorn step is exactly

```text
M |-> diag(l) * M * diag(r).
```

The owner also supplies row and column residual/Lyapunov functions, logarithmic
Radon--Nikodym generators, and the associated barrier potentials.

This is already the repository's finite multiplicative gauge-fixing mechanism.
It must sit between local Gibbs scores and the globally balanced transport
operator.

## 3. Birkhoff--von Neumann is the discrete mode resolution

For every certified bistochastic switch, Mathlib's Birkhoff theorem yields

```text
P = sum_sigma w_sigma * permutationMatrix(sigma),
w_sigma >= 0,
sum_sigma w_sigma = 1.
```

`LLM/BogoliubovSinkhornRouting.lean` transports this decomposition to expert
outputs:

```text
balancedOutput(i)
  = sum_sigma w_sigma * expertOutput(sigma(i), i).
```

Thus the correct chain is

```text
Gibbs row assignment
 -> Sinkhorn two-sided gauge balancing
 -> Birkhoff-polytope point
 -> convex resolution into permutation-routed modes.
```

The theorem boundary remains important: a convex combination of Bogoliubov or
Clifford group elements is not automatically another group element.  The
proved invariant is state-level submodule preservation under the balanced
mixture.

## 4. Poisson-Sinkhorn already supplies the primal/dual variational layer

The Poisson transport corridor proves more than normalization.

For each row, the Gibbs assignment is the unique positive minimizer of the
entropy-regularized objective.  For the full matrix problem, additive dual
potentials `alpha` and `beta` define the entropic dual objective.  The gauge

```text
alpha_i |-> alpha_i + t,
beta_j  |-> beta_j - t
```

leaves the dual objective unchanged.

For a positive bistochastic coupling `Pi`, the repository proves the exact
identity

```text
primalObjective(Pi) - dualObjective(alpha,beta)
  = epsilon * sum_ij poissonBregman(
      Pi_ij,
      exp((alpha_i + beta_j - cost_ij)/epsilon)).
```

The primal/dual gap is therefore nonnegative because it is a sum of Bregman
divergences.  This is the correct convex-analytic owner for the Sinkhorn
potentials.

## 5. Weighted adjoints are the detailed-balance owner

`Probability/FiniteMarkovWeightedAdjoint.lean` defines the stationary-weighted
balance residual

```text
diag(pi) * L - transpose(L) * diag(pi).
```

It proves the equivalence of:

1. zero weighted balance residual;
2. vanishing stationary edge currents;
3. equality with the weighted adjoint; and
4. symmetry of the stationary-whitened generator.

Consequently the correct reversible/nonreversible split is not ordinary matrix
symmetry unless the stationary weight is uniform.  It is symmetry relative to
`pi`.

This is the owner to which any spin-transformer transition kernel must be
mapped before making a detailed-balance or entropy-production claim.

## 6. Affinities, Wilson cycles, and Maximum Caliber are already connected

`ThermodynamicChiralGraphCalculus.lean` defines:

```text
logAffinity(e) = log(forwardRate(e) / reverseRate(e)),
stochasticAffinity(e)
  = log(p(src e) * forwardRate(e) /
        (p(dst e) * reverseRate(e))),
cycleCurvatureLog(C) = sum_{e in C} logAffinity(e).
```

It proves the edgewise nonnegativity kernel

```text
(x-y) * log(x/y) >= 0
```

for positive fluxes, gauge invariance of closed-cycle curvature, and the
vanishing of cycle curvature for exact/coboundary log-affinities.

`Canonical/MaximumCaliberPath.lean` then proves the path fluctuation readout

```text
P_forward(gamma) / P_backward(gamma)
  = exp(pathEntropyProduction(gamma)),
```

and recovers detailed balance from a vanishing positive cycle constraint.

The repository therefore already carries both:

```text
local weighted-adjoint balance
```

and

```text
global cycle-affinity obstruction.
```

These are complementary, not competing, formulations.

## 7. Exact, coexact, and harmonic currents supply the rotational split

The finite Hodge lane distinguishes:

```text
exact currents   = gradient/coboundary sector,
coexact currents = loop/circulation sector,
harmonic currents = simultaneous closed/coclosed kernel.
```

The repository proves closure/coclosure under the explicit complex premises,
orthogonality of the harmonic sector to exact and coexact local errors, and
protection of a Bayesian posterior lying in the harmonic stabilizer kernel.

`BayesianThermoMetricHodgeBridge.lean` connects the coexact Maximum-Caliber
current to the `d log Q` readout.  This is the finite theorem-owned form of the
irrotational/rotational separation.

## 8. The two-Gramian mass-spectrometry corridor is not incidental

The mass-spectrometry lane distinguishes two matrices:

```text
auto-Gramian:  G(Z) = Z * transpose(Z),
cross-Gramian: C(Z1,Z2) = Z1 * transpose(Z2).
```

The auto-Gramian is symmetric and has zero antisymmetric part.  A cross-Gramian
need not be symmetric; transposition exchanges the two feature slices, and
explicit witnesses show that its antisymmetric part can be nonzero.

Every directed square operator is reconstructed from

```text
K = symmetricPart(K) + antisymmetricPart(K).
```

`CausalTransferArchitecture.lean` multiplies the cross-Gramian score by a
finite log-mass KAN potential only on certified edges of a valued fragmentation
DAG.  Any nonzero transfer coefficient therefore implies:

```text
child mass < parent mass,
deltaMass > 0.
```

The directed operator is then doubled into forward/reverse sheets, converted
to a skew chiral shadow, and combined with a Moore--Penrose projectivity tensor.

This lane is a concrete finite example of the same general architecture:

```text
reciprocal metric score + oriented causal score
 -> doubled operator
 -> chiral/Hodge readout
 -> constrained transport.
```

## 9. The modular Hessian is already derived from a primitive divergence datum

`RelationalInformationCore.lean` starts from:

```text
reference state,
comparison state,
state-dependent modular generator,
information functional,
first variation,
second variation.
```

The comparison-state second variation is the metric form.  Its phase partner is
obtained by twisting one perturbation channel by the modular complex axis
`J epsilon`, which squares to minus the identity.

The owner also derives:

```text
comparison dynamics = gauge dynamics + source dynamics,
phase readout = metric readout composed with modular complex structure.
```

`Canonical/ModularHessian.lean` is an expository alias layer over these owners:

```text
modularHessian = comparison second variation,
fisherPart      = comparison metric,
vortexPart      = modularly twisted phase form.
```

The symmetric metric/Hessian channel and the skew phase/curvature channel are
therefore already separated at the operator level.

## 10. BKM is the noncommutative metric extension

The finite BKM owner proves positivity of logarithmic-mean weights, Hermitian
symmetry, positive semidefiniteness, and the commuting reduction

```text
BKM metric on diagonal observables = classical Fisher metric.
```

The Souriau--Krein metriplectic owner combines this metric-response channel with
commutator/curvature readouts on the doubled operator carrier.  Positivity is not
asserted for the indefinite Krein form without an explicit positive-response
hypothesis.

Thus the mcbal covariance/susceptibility geometry belongs naturally in the
classical commuting readout of an already larger operator metric architecture.

## 11. Frozen-drive KL mismatch is already the Information-Bottleneck modular potential

The canonical finite Information-Bottleneck stack contains:

```text
IBBase
 -> IBUpdate
 -> IBFrozenDescent
 -> IBFiniteIteration
 -> IBTrajectory
 -> IBCanonical.
```

The Blahut--Arimoto update is represented as a projective score ray followed by
a gauge section.  The frozen variational functional decreases under the frozen
BA step.  Normalize-Lipschitz data yield a global contraction estimate, and a
subunit Lipschitz bound gives Banach convergence to a fixed point.

Most importantly, `IBFrozenModularBridge.lean` proves

```text
-log(updated probability / frozen prior)
  = beta * KL(local law || frozen target law)
    + logPartitionFrozen.
```

After subtracting the partition-gauge term, the local modular potential is
exactly `beta * KL`.

This is the canonical repository analogue of the mcbal frozen-drive mismatch.
It is not merely a proposed future module.

## 12. Dikin ellipsoids already control finite optimization orbits

The Dikin lane includes scalar, information-bottleneck, Souriau, Drazin,
Apollonius, Poincare, and operator-BKM variants.

`DikinFiniteOrbitColimit.lean` proves that if

```text
|T z - x| <= K * |z - x|,
```

then every finite iterate remains in the nested Dikin ellipsoid with radius
`K^n r`.  Under a subunit radius, the orbit remains strictly inside the
positive domain.

The same file defines a BKM-Dikin quadratic form on self-adjoint operators and
proves:

```text
quadratic >= 0,
quadratic = 0 iff operator = 0,
radius-zero ellipsoid iff point = center,
BKM-isometries preserve Dikin constraints.
```

This is the finite interior-point geometry that should bound any future
mean-field/Sinkhorn iteration before a continuum convergence theorem is
attempted.

## 13. The Wasserstein/Otto--Villani status must be stated accurately

The repository contains a finite `WassersteinProximalBridge` in which a
JKO-style step is represented by a parabolic unipotent operator.  It proves:

```text
step(eta1) * step(eta2) = step(eta1 + eta2),
step(eta)^n = step(n * eta),
```

and associated finite threshold bounds.

This is not the full analytic Otto calculus, the complete Wasserstein metric
on probability measures, or the JKO convergence theorem for the heat equation.
It is a finite proximal envelope.  The distinction should remain explicit.

## 14. The exact remaining mcbal gap

After the audit, the missing bridge is much narrower than previously stated.
It is not any of Sinkhorn, Birkhoff, primal/dual convexity, detailed balance,
affinities, Hodge decomposition, modular Hessians, IB fixed points, Wasserstein
proximity, or Dikin geometry.

The missing theorem starts from a finite vector-spin stochastic kernel

```text
P(S' | S) = product_i p_i(S'_i | effectiveField_i(S))
```

and constructs its product-marginal projection `Q_m`.  It must then prove that
the deterministic mean-field update is exactly the expectation parameter of
that projected product law:

```text
m'_i = E_{Q_m}[S'_i].
```

The next map must identify the interaction/transition matrix used in that model
with a repository transport owner:

```text
raw Gibbs row kernel
 -> optional Sinkhorn balancing certificate
 -> Birkhoff permutation-simplex decomposition
 -> weighted-adjoint reversible part
    plus cycle-affinity/Hodge rotational part.
```

Only after these maps exist can one prove, rather than merely compare:

```text
mcbal product-marginal mean field
 -> repository Gibbs/Sinkhorn/MaxCal update,

mcbal frozen-drive KL mismatch
 -> canonical IB modular potential,

mcbal covariance response
 -> commuting Fisher/BKM Hessian,

mcbal housekeeping entropy production
 -> weighted current-affinity quadratic/cycle readout,

mcbal contractive iteration
 -> Dikin-confined Banach trajectory.
```

## 15. Corrected corridor

The corrected architecture is therefore

```text
stochastic vector-spin transition kernel
 -> product-marginal projection
 -> expectation/magnetization coordinates
 -> local Gibbs row assignment
 -> entropy-regularized primal minimizer
 -> Sinkhorn left/right diagonal gauge fixing
 -> bistochastic coupling
 -> Birkhoff--von Neumann permutation mixture
 -> weighted-adjoint reversible sector
    + log-affinity cycle obstruction
 -> exact/coexact/harmonic Hodge split
 -> symmetric/cross-Gramian operator split
 -> mass/log-mass causal transfer
 -> modular log potential
 -> divergence second variation / modular Hessian
 -> Fisher/BKM metric and phase twist
 -> Souriau metric/commutator dynamics
 -> BA/IB frozen-target descent
 -> finite JKO/proximal envelope
 -> Dikin-confined fixed-point iteration.
```

The repository owns every arrow after the product-marginal projection in one or
more finite theorem surfaces.  The development frontier is to construct the
explicit intertwiners from the mcbal kernel into those surfaces, not to replace
or duplicate them.

## Public theorem-owner map

```lean
import InfoGeometry.LLM.McbalFullNativeCorridor
```

The imported owner aliases the exact native theorems without changing their
hypotheses or claiming that the final mcbal intertwiner already exists.
