# Information Carnot cycle: theorem contract

Task date: 2026-11-18. Base: `08c34e03f610b452e03422037949196dc7d92d6d`.
The exact initiating message is preserved in
`docs/intake/information-carnot-20261118/prompt.txt`; its manifest records the
UTF-8 checksum. This contract distinguishes mathematical constructions from
the requested physical interpretations. Acceptance is recorded separately in
`INFORMATION_CARNOT_VALIDATION.md`.

## 1. Extracted mathematical questions

| Intake motif | Exact mathematical question | Disposition in this change |
| --- | --- | --- |
| Partition and normalization | Is `Z=Tr(exp K)` positive, does its normalized full real matrix have trace one, and what is its actual logarithm? | Native real CFC and full matrix exponential construction. |
| Information Carnot cycle | Can two self-adjoint Hamiltonians be connected by actual smooth isotherms and reciprocal scale adiabats, with trace-defined heat/work integrals? | Construct the paths and derive their integral budgets. No commutation of the endpoint Hamiltonians is imposed. |
| Expansion/contraction piston | Which scaling changes the normalized state, and which scaling disappears on normalization? | Separate common amplitude, Hamiltonian/temperature scaling, and mixing toward the isotropic state. |
| Radial direction orthogonal to orbit | Is the displacement from the isotropic state perpendicular to a conjugation tangent? | Full real finite matrices, symmetric state, Hilbert--Schmidt pairing. This is a metric-specific theorem. |
| Radial states and Gibbs normalization | Can a radial mixture be realized by an explicit self-adjoint Gibbs exponent? | Its actual CFC logarithm reconstructs the full matrix for `0≤r<1`, even when the initial state is singular. |
| Constant-entropy leaves | Which actual group action preserves entropy? | Native real unitary conjugation of Gibbs exponents; distinguish an orbit from a complete entropy level set. |
| Metriplectic breather | Can an isolated entropy-producing solution return to its initial state? | Construct Gram Onsager response and prove a no-return implication from the actual gradient and solution equation. |
| NESS and Wilson loops | Does a noncommutative loop itself give stationary entropy production? | No such implication is supplied by the inspected owners; stationary dynamics, fluxes, reservoirs and a positive production functional remain required. |
| Forward/backward causal waves | Does algebraic reflection produce a causal propagator or a wavefront PDE? | No such map is constructed here; the existing algebraic reflection owners remain distinct. |
| Weyl/Gromov--Witten/volume | Does a thermodynamic trace partition equal an enumerative or localization partition? | Existing calibration fields are inspected; a derived identification remains open. |
| Spacetime and Goldstone modes | Does the finite operator geometry construct a spacetime metric, causal front or symmetry-breaking excitation? | Interpretation/open theorem debt, with no promotion from the finite results. |

## 2. Owner-first search and reuse

Search included filenames, related declaration terms, imports and consumers in
the repository-owned Lean tree, the pinned Mathlib source, and the maintained
`context_preflight.py` navigation packet. The local packet reported no installed
declaration-DAG index or manifest. No fresh graph coverage is claimed. Generated
reports and personal/project history were used only to locate owners.

| Existing owner | Actual content inspected | Use or boundary |
| --- | --- | --- |
| `Detector/InformationCarnotCycle.lean` | Scalar efficiency/power relations and a separate Peirce identity packet. | Does not provide the Gibbs-state paths or heat/work integrals constructed here. |
| `OperatorAlgebra/NoncommutativeDuhamelFrechetBridge.lean` | The native Banach-algebra exponential derivative and its ordered Duhamel integral. | Reused for arbitrary real matrix tangent directions. |
| `OperatorAlgebra/NoncommutativeDuhamelContinuityReduction.lean` | Continuity needed to identify the Duhamel derivative. | Reused; no assumed derivative formula or commuting replacement. |
| `Canonical/SouriauHilbertSchmidtOnsager.lean` | Real `Tr(A.transpose*B)` and its symmetry/nonnegativity on the full matrix algebra. | Reused as the precise radial/orbit metric. Its stored kernel packet is not used to claim a constructed dissipative flow. |
| `Physics/MatrixTraceBimodulePairingNative.lean` | Ordered left/right matrix actions, commutator action, cyclic trace pairing. | Reused for orbit tangents and orthogonality. |
| `Thermodynamics/FiniteEntropyLeaves.lean` | Conjugation preserves cyclic trace readouts. | Reused for actual real matrix unitary transport. |
| `Physics/FiniteMetriplecticDynamics.lean` | GENERIC velocity and pointwise algebraic rate laws under explicit skewness, positivity and degeneracy inputs. | Reused with the constructed operator `A†A`; the new owner supplies the chain-rule and return-segment implications. |
| `Topology/CanonicalRapidityAngleMetriplecticFlow.lean` | Explicit scalar cylinder contraction and angle translation, with composition, derivatives and limit. | Not identified with a Bloch density or a physical spacetime without a map. |
| `Physics/SouriauEntropyFoliation.lean` | Finite Gibbs entropy/permutation invariance and scalar dilaton readouts. | Finite permutation transport is not substituted for the full matrix orbit here. |
| `Canonical/MatrixEntropyUnitaryOrbit.lean` | Complex matrix CFC entropy and native unitary invariance. | Source precedent; the current carrier remains real with no external scalar imaginary unit. |
| `Canonical/WeylEntropyShiftBridge.lean` | Globally positive readout and homogeneity for every real scale, including zero. | A nonzero weight is impossible on an inhabited carrier; the new obstruction theorem records this. Its logarithm is not automatically von Neumann entropy. |
| `Canonical/WeylGaugeGWProjectiveScaleCalibration.lean` | Calibration includes volume/partition equality fields. | Equality fields are assumptions, not an enumerative Gromov--Witten construction. |
| `Topology/ThermodynamicGauge.lean` | An arbitrary ring commutator is named entropy production; zero is equivalent to commutation. | It has no order, nonnegativity, stationary measure or reservoir balance from that definition alone. |
| `Topology/WilsonLoopThermodynamics.lean` | Ordered products of finite transport steps. | Does not construct continuous path-ordered holonomy or positive irreversible entropy production. |

The trace-action owner's umbrella Mathlib import is replaced by its four
actual native imports. Every declaration and proof below those imports is
unchanged; the changed owner is included in native compilation and the full
declaration audit. No existing theorem or dependency pin is weakened. The categorical infrastructure
map was consulted; no universal property, analytic limit or representation
equivalence is inferred from the finite matrix constructions.

## 3. Full real Gibbs calculus

Carrier: `Matrix n n ℝ` for an arbitrary finite index type, with native L2
operator norm, real star/transpose, matrix order and continuous functional
calculus. Nonempty index type is required for a positive trace partition.

For a self-adjoint exponent `K`, define

\[
 Z(K)=\operatorname{Tr}(e^K),\qquad
 \rho(K)=Z(K)^{-1}e^K,\qquad
 \psi(K)=\log Z(K),\qquad
 S(K)=-\operatorname{Tr}\bigl(\rho(K)\log\rho(K)\bigr).
\]

The strict positivity, trace-one normalization and logarithm are derived using
native APIs. In particular,

\[
 \log\rho(K)=K-\psi(K)I,\qquad
 S(K)=\psi(K)-\operatorname{Tr}(\rho(K)K).
\]

The Fréchet derivative of the partition is obtained from the ordered Duhamel
insertion. Cyclicity of trace and exponential addition for scalar multiples
of `K` collapse the insertion:

\[
 DZ_K[A]=\operatorname{Tr}(e^K A).
\]

For an actual differentiable curve with `K'(t)=A`, the exposed Massieu
derivative theorem gives

\[
 \frac{d}{dt}\psi(K(t))=\operatorname{Tr}(\rho(K(t))A).
\]

There is no `Commute K A` hypothesis. Along a differentiable self-adjoint
curve with actual normalized-state derivative `R`,
`S'=-Tr(R*K)`. The physical inverse-temperature convention is `K=-βH` and
Boltzmann's constant is set to one.

## 4. Constructed four-stroke cycle

On a nonempty finite index type, take `β>0`, `0<c<1`, and arbitrary self-adjoint matrices `H₀,H₁` on the same
full carrier. The hot and cold temperatures are `T_h=1/β` and `T_c=c/β`.
The four corners are

| Corner | Hamiltonian | Inverse temperature | Density |
| --- | --- | --- | --- |
| A | `H₀` | `β` | `ρ(-βH₀)` |
| B | `H₁` | `β` | `ρ(-βH₁)` |
| C | `c H₁` | `β/c` | Exactly the density at B |
| D | `c H₀` | `β/c` | Exactly the density at A |

The hot isotherm is `H(t)=H₀+t(H₁-H₀)` for `0≤t≤1`; the cold isotherm is the
same construction at the reversed scaled endpoints. The density curve is
constructed by the real matrix exponential. Its continuous differentiability
and heat/work integrability are proved, rather than stored as cycle fields.
The Hamiltonians can fail to commute at the endpoints or at intermediate times.

Each adiabat uses `a(t)=a+t(b-a)>0`, Hamiltonian `a(t)H`, and inverse
temperature `β/a(t)`. Their product is fixed, so the entire density is fixed.
These are controlled energy-scale changes; the code does not call them
autonomous unitary dynamics or a derived Weyl gauge of spacetime.

For `U=Tr(ρH)` the actual ordered currents are

\[
 \dot Q=\operatorname{Tr}(\dot\rho H),\qquad
 \dot W_{\mathrm{on}}=\operatorname{Tr}(\rho\dot H),\qquad
 \dot U=\dot Q+\dot W_{\mathrm{on}},\qquad \dot S=\beta\dot Q.
\]

Native interval integration gives the heat and work budgets on both
constructed isotherms. On each positive scale segment, the full density is
fixed, and the work-current integral equals `(b-a)Tr(ρH)`. These results yield
the four-stroke endpoint budget. With
`ΔS=S(-βH₁)-S(-βH₀)`,

\[
 Q_h=\frac{\Delta S}{\beta},\quad
 Q_c=-\frac{c\Delta S}{\beta},\quad
 W_{\mathrm{out}}=Q_h+Q_c=(1-c)Q_h,\quad
 \eta=1-c=1-\frac{T_c}{T_h}.
\]

The efficiency statement requires a nonzero entropy stroke. Positive work
requires `ΔS>0`; it is not inferred merely from two distinct or noncommuting
Hamiltonians. This is an equilibrium-path model of an ideal reversible Carnot
cycle. A quasistatic limit of bath-coupled dynamics and positive finite-time
power are outside the construction.

## 5. Three distinct meanings of scale

For the radial results, `n` is a positive integer dimension and the carrier is
`Matrix (Fin n) (Fin n) ℝ`.

1. **Common weight amplitude:** `N(cA)=N(A)` for nonzero `c`, where
   `N(A)=A/Tr(A)`. Positive `c` preserves the positive weight cone. This gauge
   cannot by itself change the normalized entropy. Its interpretation as a
   trace-one state requires `Tr(A)≠0`; for a positive input, use `Tr(A)>0`.
2. **Energy-scale adiabat:** `(H,β)↦(cH,β/c)` preserves the entire Gibbs
   exponent and density while changing energy and temperature.
3. **Radial mixing of a normalized state:**
   `R_r(ρ)=rρ+(1-r)I/n` changes a noncentral density when `r≠1`. For a positive
   trace-one input and `0≤r≤1`, it preserves positivity and trace one, and
   `R_r∘R_s=R_(rs)`.

For symmetric trace-one matrices, the precise radius law is

\[
 \operatorname{Tr}(R_r(\rho)^2)
 =\frac1n+r^2\left(\operatorname{Tr}(\rho^2)-\frac1n\right).
\]

The excess purity is the Hilbert--Schmidt square of `ρ-I/n`. It is strictly
positive away from the isotropic state. A strict inward mix lowers purity.
This purity result is not relabeled as a general von Neumann entropy
monotonicity theorem. An outward inverse with `r>1` is not asserted to preserve
the entire positive state space.

The infinitesimal conjugation direction considered here is the actual
commutator `[K,ρ]`. A skew `K` and symmetric
`ρ` make it symmetric and trace zero. Cyclic trace proves

\[
 \langle\rho-I/n,[K,\rho]\rangle_{HS}=0.
\]

A concrete noncommuting real two-by-two pair verifies that this orthogonality
does not force the orbit direction to vanish. Real two-by-two symmetric states
are not silently called the complete complex-qubit Bloch ball. A realified
qubit needs its internal complex-structure commutant and trace convention.

### Exact pointwise connection from radial states to Gibbs exponents

The `RealMatrixGibbsRadialChart` owner supplies a concrete map between the
state constructors. If `ρ` is positive semidefinite with trace one, `n≠0`, and
`0≤r<1`, the central contribution makes `R_r(ρ)` strictly positive. Its native
CFC logarithm is a self-adjoint exponent:

\[
 K_r=\log R_r(\rho),\qquad \rho(K_r)=R_r(\rho).
\]

The normalization identity is proved for every strictly positive trace-one
real matrix using the native exponential/logarithm inverse law. Thus the radial
mixture itself, including every matrix entry, is realized by the Gibbs
constructor. This is a pointwise state map; continuity, differentiability and
entropy monotonicity of this logarithmic parameterization are not supplied by
these four theorems. At `r=1`, a singular input lies outside the faithful-log
chart.

### Real entropy-preserving orbits and an internal phase operator

The new `RealMatrixGibbsOrbit` owner proves exponential naturality, partition
and Massieu invariance, full density covariance, and actual CFC entropy
invariance for self-adjoint exponents in nonzero dimension under native real
unitary (orthogonal) conjugation. The observable
expectation is invariant when both exponent and observable are transported.
Radial mixing, trace normalization and the Gibbs density construction preserve
commutation with any chosen internal real operator `J`. If `J²=-I`, these three
operations therefore preserve its complex-linear commutant. Preservation of
that same fixed commutant by orthogonal conjugation requires an additional
compatibility condition on the conjugating matrix; it is not asserted here.
No complete Bloch-ball chart or identification of trace conventions is inferred
from these commutant results. Arbitrary thermodynamic tangent matrices remain
unrestricted by a commutation premise.

### Zero-scale obstruction in the existing homogeneous-readout interface

The existing `WeylHomogeneousEntropy` requires both global positive readout
and a homogeneity law for all real scales. At scale zero, a nonzero natural
weight forces the readout of `scale 0 x` to vanish, contradicting its positivity.
The obstruction theorem proves the weight must be zero whenever an input `x`
exists. Thus the weight-one/two specializations cannot instantiate a positive
physical piston under the current interface. The new construction uses actual
positive matrix domains and nonzero normalization scales; it does not assume
an inhabitant of that impossible positive-weight package. A redesign of the
legacy scaling API is separate from this change.

## 6. Isolated metriplectic dynamics and periodicity

The analytic owner uses arbitrary real Hilbert spaces `E,F`, a skew operator
`J(x)`, a bounded real-linear map `A(x):E→F`, and actual energy/entropy gradients. It
constructs the positive Onsager operator `A(x)†A(x)` in the existing GENERIC
velocity:

\[
 \dot x=J(x)\nabla H(x)+A(x)^*A(x)\nabla S(x).
\]

With `J∇S=0`, the native chain rule gives
`dS/dt=‖A∇S‖²≥0`. With `A∇H=0`, it also gives `dH/dt=0`.
These are implications for an actual differentiable solution satisfying the
explicit gradient and evolution equations. Existence, uniqueness and global
state-domain preservation are not supplied by those implications.
The skew reversible operator is distinct from the fixed internal complex
structure discussed above; no identification of these two uses of `J` is made.
Skewness alone also does not construct a Poisson bracket satisfying Jacobi.

If endpoint entropy agrees, monotonicity makes entropy constant between the
endpoints. Derivative uniqueness then forces `A∇S=0` at every interior point.
A positive-period solution has zero dissipative force at every time and only
the reversible velocity remains. Periodicity need not make that reversible
velocity zero. This does not exclude a heat engine with external parameter
control and reservoirs: the working body's entropy can decrease during heat
rejection while the total isolated-system entropy obeys its balance law.

## 7. Dependency order and open connections

The formal dependency chains are:

- Native real CFC and the existing noncommutative Duhamel derivative → actual
  Gibbs normalization/logarithm → first-law and entropy differentials → smooth
  isotherm integrals and reciprocal-scale adiabats → four-stroke work/efficiency.
- Existing ordered trace actions and Hilbert--Schmidt pairing → normalized
  radial mixing → purity and radial/orbit orthogonality; positive central
  contribution plus native CFC logarithm → exact Gibbs realization of radial states.
- Existing GENERIC velocity plus native adjoints → constructed Gram response
  → actual entropy derivative → monotonicity → return/periodicity obstruction.

The logarithmic chart connects isotropic radial states to the actual Gibbs
constructor. The present change does not identify either affine Gibbs
isotherm with that radial mixing path, and it does not instantiate the Gram
evolution with Gibbs entropy and a specified pair of reversible and dissipative
operators. Those identifications require additional state maps and compatibility
theorems.

The following arrows remain unconstructed: thermodynamic trace partition to
Gromov--Witten invariants or localization volume; radial mixing to a physical
spacetime metric; an orbit to a Goldstone excitation spectrum; finite Wilson
products to a stationary open-system current; algebraic branch exchange to a
causal propagator with boundary conditions. A common name or an informal
analogy is not inserted as a dependency edge.

## 8. Research context

The mathematics in this change is proved from native Mathlib and repository
owners. Primary literature helps set interpretation and scope, rather than
serving as a Lean assumption:

- G. P. Beretta, *Quantum thermodynamic Carnot and Otto-like cycles for a
  two-level system*, [quant-ph/0703261](https://arxiv.org/abs/quant-ph/0703261).
  The controlled energy-gap and thermodynamic distinctions motivate checking
  the strokes, not just an efficiency expression.
- A. Bloch, P. Morrison and T. Ratiu, *Gradient flows in the normal and Kähler metrics and triple bracket generated metriplectic systems*,
  [arXiv:1208.6193](https://arxiv.org/abs/1208.6193). Reversible and dissipative
  components and their conserved quantities are distinct mathematical inputs.
- F. Barbaresco, *Jean-Marie Souriau's Symplectic Foliation Model of Sadi
  Carnot's Thermodynamics*, [Entropy 27 (2025), 509](https://www.mdpi.com/1099-4300/27/5/509).
  An invariant entropy is constant on each relevant orbit; an identification
  of an entire entropy level with one orbit requires additional separation
  hypotheses and is not used here.

## 9. Native theorem entry points

All paths below are relative to `lean/InfoGeometry`. These are concrete
declarations to consume, rather than additional interpretation interfaces.

| Owner | Principal entry points |
| --- | --- |
| `Thermo/RealMatrixGibbs.lean` | `partition_pos`, `density_strictlyPositive`, `log_density`, `entropy_eq_massieu_sub_expectation`, `hasFDerivAt_partition`, `partitionDifferential_apply`, `hasDerivAt_entropy_curve` |
| `Thermo/RealMatrixCarnot.lean` | `contDiff_state_affine`, `affineHeat_integral_eq_hotHeat`, `affineWork_integral_eq_hotWorkOn`, `affineHeat_integral_eq_coldHeat`, `affineWork_integral_eq_coldWorkOn`, `state_scaling_segment`, `scalingWorkOn_integral`, `efficiency_eq_one_sub_scale`, `cycleWork_pos` |
| `Thermo/RealDensityRadialFlow.lean` | `traceNormalize_smul`, `radialMix_posSemidef`, `radialMix_comp`, `radialMix_purity`, `radialMix_purity_lt`, `radialDirection_orthogonal_commutator`, `exists_noncommuting_symmetric_orbit` |
| `Thermo/RealMatrixGibbsOrbit.lean` | `density_unitary_conjugate`, `expectation_unitary_conjugate`, `entropy_unitary_conjugate`, `density_commute`, and the radial owner's `radialMix_commute` / `traceNormalize_commute` |
| `Thermo/RealMatrixGibbsRadialChart.lean` | `density_log_of_trace_one`, `uniformDensity_posDef`, `radialMix_strictlyPositive`, `radialMix_gibbs_realization` |
| `Thermo/GramMetriplecticNoReturn.lean` | `entropy_rate_eq_norm_sq`, `hasDerivAt_energy_zero`, `entropy_monotone`, `no_state_return_of_dissipative_force_ne_zero`, `dissipative_force_eq_zero_of_periodic`, `periodic_velocity_eq_reversible` |
| `Canonical/WeylEntropyScaleObstruction.lean` | `weight_eq_zero_of_global_positivity`, `entropy_scale_eq_of_global_positivity` |

The finite trace-action owner's import refinement changes no theorem entry
point or argument order.
