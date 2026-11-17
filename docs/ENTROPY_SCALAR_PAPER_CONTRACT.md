# Finite-capacity entropy paper: mathematical contract

## Source and revision

This task reviews Florian Neukart, Eike Marx, and Valerii Vinokur,
*Finite-Capacity Spacetime and Entropic Contributions to Cosmological Structure
Formation*, Physics **8** (2026), 49,
<https://doi.org/10.3390/physics8020049>.

The source is the user-supplied 32-page `physics-08-00049-v3.pdf`, whose SHA-256 is
`fe765085e507470ba99433fe9afb80d46f3270957339b8244d1e71e53230a0c7`.
All page references below are both printed and PDF page numbers. The attached
PDF, rather than a subsequently updated HTML article, fixes the equations under
review. Its metadata records a 10 June 2026 modification. The paper is licensed
CC BY by its authors. The PDF itself is not part of this source change.

Repository discovery starts from upstream
`08c34e03f610b452e03422037949196dc7d92d6d`. Lean and Mathlib pins remain those of
the repository. The mathematical targets below are candidates until native
verification and independent review are recorded in the validation section.

## Formal intent

The target is the canonical mathematical content of the displayed equations:
the full scalar stress tensor, its energy and spatial trace, sourced kinetic
energy balance, and the proposed spherical mass profile. The target does not
assume the paper's pressureless-matter conclusion. Pointwise tensor identities,
real differentiation, finite weighted averages, and one-sided/asymptotic limits
have separate contracts.

The quantum side retains full noncommutative matrix algebras through the existing
actual-CFC entropy owner. The classical scalar-field tensor has real entries in
a fixed four-dimensional orthonormal frame; this is the carrier of the paper's
displayed scalar stress, not a replacement for its quantum matrix dynamics.

## Existing owners inspected

| Owner | Actual content | Boundary |
| --- | --- | --- |
| `Canonical.MatrixEntropyUnitaryOrbit` | `matrixEntropy_unitary_conjugate` preserves `-Re(trace(P * CFC.log P))` under arbitrary unitary conjugation of a strictly positive finite complex matrix | Strict positivity is required; no entropy production or gravitational conversion is derived |
| `OperatorAlgebra.PeirceSpine.PeircePositiveCollision` | `density_recovery_iff_trivial` characterizes recovery of every density matrix from pinching by `P = 0` or `P = 1` | Information loss is distinct from an entropy-production rate or source law |
| `Quantum.FinitePartialTrace` and `OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal` | Actual partial trace, trace preservation, and positive normalized marginal states | A microscopic interaction/source model still needs to be specified |
| `Inference.FiniteGibbsThermodynamicIdentity` | Entropy of strictly positive normalized finite distributions is bounded by `log(card)` | No spectral identification with matrix entropy or spacetime area law is supplied by this result alone |
| `Physics.FisherKreinLorentz` | Constructs `fisherKreinLorentz4` with signature `(-,+,+,+)` and proves its entries | Fixed-frame metric algebra; no continuum field equations |
| `Canonical.FisherKreinVielbeinEinsteinBridge` | Connects this metric to the existing tetrad reference convention | Its further Einstein readouts have explicit calibration hypotheses |
| `Canonical.StressEnergyTensor` | Symmetrizes supplied spinor bilinear arrays | A different field model from a scalar kinetic tensor |
| `Physics.Section38StressEnergyDomainSeparation` | Finite matrix stress and supplied connection-variation tables | No continuum action variation |
| `SuperMetriplectic.DarkEnergyMapping` | Friedmann-style equalities supplied as structure fields | Does not construct scalar cosmology or prove pressureless behavior |
| `Analysis.LogHomogeneousPotential` | Genuine one-variable logarithmic derivatives | Not an identification with the three-dimensional Euclidean Laplacian |

Searches covered canonical `lean/InfoGeometry` and `lean/Omega`, related source
mirrors, imports and consumers, tooling/entrypoints, selected generated indexes,
and the pinned Mathlib sources. Queries included actual entropy/CFC operations,
unitary conjugation, partial trace, scalar stress, FLRW/Friedmann, dust/stiff
behavior, slow roll, spherical mass/density, radial Laplacians, the paper title,
author, and DOI. No existing same-paper PR or scalar-stress owner was found in
that bounded search. No freshness claim is made for a live declaration graph.

## Claim ledger

| Paper location | Displayed claim or mechanism | Mathematical disposition |
| --- | --- | --- |
| p. 4, local updates and Eq. (1) | Separate local unitary conjugations followed by a fixed entropy average | Existing actual-CFC entropy invariance preserves each faithful local entropy; a new open-system or changing-coarse-graining mechanism is needed for production |
| pp. 5, 9, Eqs. (2), (9), (11) | Positive coefficient of `g^{mu nu} d_mu S d_nu S` with signature `(-+++)`, but positive canonical stress | The printed kinetic sign and stress convention disagree; coefficient normalization in Eq. (9) also needs reconciliation |
| p. 12, Eq. (22) | Mean pressure `lambda/6 * (u^2 - q)` from Eq. (11) | The actual spatial trace is `lambda/2 * u^2 - lambda/6 * q` |
| p. 12, Eqs. (23)-(24) | Equal averaged temporal/spatial squares yield dust | The corrected trace gives `3 * meanPressure = energy`; zero mean pressure instead requires `q = 3 * u^2` when the coupling is nonzero |
| p. 11, Eqs. (19)-(20) | Add `-lambda * Gamma` to canonical pressure while retaining the stated exchange balance | Native differentiation gives residual `-3 * H * lambda * Gamma`; the claimed balance is not an identity |
| p. 1, abstract | Source-free equation together with nontrivial slow roll | For positive Hubble coefficient, the equation fixes `abs(u') = 3 * H * abs(u)` |
| pp. 22-23, Eqs. (35)-(36) | A negative temporal kinetic coefficient gives the displayed positive Hamiltonian | The actual velocity derivative and Legendre transform have the opposite sign |
| p. 7, Eq. (8) | Smooth saturation mass profile | Its two terms simplify to `2 * eta * s * r^2 / (r+s)`; differentiate this actual mass function |
| pp. 1, 7-8, 19 | Finite core and inner flat rotation claims | Eq. (8) has an inner `1/r` density cusp and an outer `1/r^2` envelope; an outer constant circular speed is an analytic consequence of the proved speed-squared formula, not a separately formalized speed-limit theorem |
| p. 18 | `S0 + S1 * log r` is spherically harmonic | The three-dimensional radial differential expression is `S1/r^2`; a native Euclidean-Laplacian realization is separate |
| pp. 14, 30, Eq. (25), Eq. (A6), Appendix E | Mutually consistent perturbation equations | The printed wavenumber coefficients differ in sign and magnitude; the update also needs its Hubble damping reconciled |
| pp. 24-25 | Small positive running gives acceleration | For the displayed approximation `q = (1 - xi*beta)/2`, acceleration needs `xi*beta > 1` |
| pp. 27, 30 | Fits and simulations validate the model | Empirical claims are not reproduced by this formalization; the attachment does not identify the promised companion repository by URL or DOI |

## New theorem contracts

### Full canonical scalar stress

Use `v : Fin 4 -> Real`, the existing Fisher-Krein metric `g`, and real coupling
`lambda`. Construct the full native matrix

`T(mu,nu) = lambda * (v(mu)*v(nu) - g(mu,nu)*K(v)/2)`,

where `K(v)` is the actual double metric contraction. Derive symmetry,
off-diagonal entries, `K = -v(0)^2 + q`, energy `T(0,0)`, and the mean of the
three spatial diagonal entries. Retain arbitrary spatial and time-space
off-diagonal terms. Finite weighted averages act on full matrices before their
energy and trace readouts.

Mean spatial stress becomes perfect-fluid pressure only after establishing
isotropy. Neither a finite average nor equality of two quadratic contributions
establishes isotropy, zero energy flux, dust evolution, or propagation speed.

### Kinetic derivative and source balance

Use native `HasDerivAt` and `deriv`. Derive the energy derivative along a
homogeneous covector and prove the conditional source balance from the explicit
equation `u' + 3*H*u = Gamma`. Prove the exact residual for the paper's modified
pressure. Derive a quadratic Lagrangian's velocity derivative and Legendre
energy, connecting the result to the constructed tensor energy. No continuum
variational principle or global FLRW solution is claimed.

### Spherical mass profile

Use real radius `r > 0`, saturation radius `s > 0`, and amplitude `eta`.
Derive the mass derivative with `HasDerivAt`, define density from that actual
derivative divided by `4*pi*r^2`, and establish its formula and limits. Positive
amplitude yields a divergent central density. These are consequences of the
specified phenomenological profile; no field-to-halo derivation is supplied.

## Declaration map

The names below are relative to the indicated `InfoGeometry.Physics` namespace.
They describe theorem statements; acceptance evidence is recorded separately.

| Namespace | Declarations | Exact consequence |
| --- | --- | --- |
| `CanonicalScalarStress` | `metric_mul_self`, `derivativeContraction_eq`, `stressTensor_offdiag` | The reused metric is its own inverse, its contraction is `-u^2 + q`, and arbitrary mixed stress components remain `lambda * v(i) * v(j)` |
| `CanonicalScalarStress` | `energyDensity_eq`, `meanSpatialStress_stressTensor` | Actual tensor readouts are `lambda/2 * (u^2+q)` and `lambda/2 * u^2 - lambda/6 * q` |
| `CanonicalScalarStress` | `stressTensor_noncommuting_examples` | Two explicitly constructed stress matrices do not commute under ordinary native matrix multiplication; this is not covariant tensor composition |
| `CanonicalScalarStress` | `meanSpatialStress_eq_zero_iff`, finite weighted counterparts | Zero spatial trace has the factor-three quadratic balance when the coupling is nonzero; no isotropic-fluid interpretation is inferred |
| `ScalarKineticBalance` | `hasDerivAt_kineticLagrangian`, `legendreEnergy_eq_energyDensity`, `legendreEnergy_neg_eq_neg_energyDensity` | Actual velocity differentiation and the Legendre expression fix the energy sign |
| `ScalarKineticBalance` | `homogeneous_source_balance`, `source_pressure_residual`, `effective_pressure_balance` | The explicit scalar ODE determines the exchange term, the printed-pressure residual, and the corrected effective pressure for nonzero Hubble coefficient |
| `ScalarKineticBalance` | `eq_zero_of_source_free_slow_roll`, `hasDerivAt_scaled_energy_zero`, `scaled_energy_constant` | A quantitative slow-roll factor below three forces zero temporal derivative; the source-free ODEs preserve `a^6 * rho`, with global constancy requiring the ODEs at every real time |
| `SphericalMassProfile` | `twoTermMass_eq_mass`, `hasDerivAt_mass`, `density_eq` | Simplify the printed mass and differentiate that actual function before defining its spherical density |
| `SphericalMassProfile` | `tendsto_radius_mul_density_zero`, `tendsto_density_zero_atTop`, `not_tendsto_density_zero_finite`, `tendsto_radius_sq_mul_density_atTop` | Inner coefficient `eta/pi`, positive-parameter central divergence, absence of a finite central limit, and outer coefficient `eta*s/(2*pi)` |
| `SphericalMassProfile` | `circularSpeedSq_eq` | Exact formula `2*G*eta*s*r/(r+s)` on positive radius and saturation scale |

## Validation

Independent mathematical and source reviews accepted the three owner contracts,
including the full tensor, the derivative hypotheses, and the one-sided halo
limits. The staged proof-proxy gate passed. Strict placeholder checks found no
hard findings; the semantic-vacuity error gate passed, retaining three advisory
warnings for elementary component/linearity lemmas. The workflow also passed
independent source review and YAML/embedded-Python syntax checks.

Exact-source native compilation and the declaration axiom audit are pending.
The maintained checker is queued on the shared build lock; the queued command
is not compilation evidence. The focused workflow repeats those checks at the
repository's exact pins and requires zero warnings in the three new owners.
The installed publication gate and whole-root dependency integration are
separate requirements; no whole-repository build result is claimed here.
