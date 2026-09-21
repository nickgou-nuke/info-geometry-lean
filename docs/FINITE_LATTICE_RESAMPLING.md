# Finite lattice gauge model with global Gibbs resampling

## Mathematical scope

The model uses a finite edge set, a finite face set, and a finite gauge group.
The group need not be commutative. Each face has four incident, oriented edges.
The holonomy is the ordered product of two forward links and two inverse links.
Vertex gauge transformations conjugate each face holonomy at its base vertex.

The action counts faces with nonidentity holonomy. This conjugation-invariant
finite-group plaquette cost is not an implementation of the SU(3) Wilson trace
action. Its Gibbs weights are `exp (-beta * action) / partition`; their strict
positivity, normalization, and gauge invariance are supplied by explicit proofs.

## Dependency order

1. `LatticeGauge/FinitePlaquette.lean`: incidence, link variables, gauge action,
   holonomy covariance, and gauge-invariant nonnegative plaquette action.
2. `LatticeGauge/FiniteGibbsModel.lean`: normalized equilibrium weights, reusing
   `Probability/FiniteGibbsDeformationReadout.lean`.
3. `Probability/FiniteResamplingGap.lean`: global-refresh kernel, detailed
   balance, stationarity, weighted symmetry, and the Dirichlet-form identity.
4. `Probability/FiniteResamplingSpectrum.lean`: native mathlib spectrum of the
   refresh Hamiltonian, including nonzero eigenvector witnesses.
5. `LatticeGauge/FiniteResamplingDynamics.lean`: the assembled lattice model.
6. `LatticeGauge/FiniteResamplingTests.lean`: a single square with both the
   permutation group on three elements and the cyclic group of order two.

## Dynamics and exact gap

For equilibrium weights `mu`, the transition kernel is `K(x,y) = mu(y)`:
one step refreshes the **entire configuration**, not just one link. Its Markov
operator is the weighted-mean projection `P`; the unit-rate continuous-time
generator is `P - I`, and the positive Hamiltonian is `H = I - P`.

The source proves

```
<f, H f>_mu = Var_mu(f) = (1/2) sum_x sum_y mu(x) K(x,y) (f(x)-f(y))^2.
```

It also proves `spectrum Real H = {0,1}` when there are at least two
configurations. Thus the spectral gap is exactly one, not merely the positivity
of a quantity named "gap". The exact-spectrum statement requires a nonempty
edge set and a nontrivial gauge group. For a one-state space the Hamiltonian is
zero; there is no excited eigenvalue. The tests cover this boundary case.

A separate reusable minorization lemma gives a Poincare lower bound `delta`
whenever `K(x,y) >= delta * mu(y)`. No such minorization is asserted for local
single-link dynamics.

## What is not claimed

The gap comes from the chosen global refresh dynamics and its time normalization.
The same gap occurs for the abelian example. Noncommutativity, a nonzero Lie
bracket, an off-diagonal coupling, and positivity of an individual energy do not
by themselves furnish a uniform spectral lower bound above a vacuum.

This model supplies neither local heat-bath mixing estimates nor continuum
Yang-Mills construction, reflection positivity, confinement, or a physical mass
gap. No infinite-volume or continuum passage is performed. Those obligations
cannot be replaced by the finite refresh spectrum or by a categorical colimit
without further theorems.

## Verification

The new modules contain proof scripts without placeholders. Kernel verification
is pending the repository's shared build lane; this document does not certify
successful compilation.

```
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.LatticeGauge.FiniteResamplingTests
```
