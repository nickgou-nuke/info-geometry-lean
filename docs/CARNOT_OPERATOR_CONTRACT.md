# Carnot intake: normalized scale, unitary orbits, and replacement relaxation

Date: 2026-11-18. Base: `08c34e03f610b452e03422037949196dc7d92d6d`.
Scope: full finite matrix algebra, native linear maps, matrix positivity,
and explicit trace identities. This contract distinguishes the implemented
operator bridge from the thermodynamic and geometric interpretations.

The subsequent weighted-adjoint and detailed-balance extension is specified
in `REPLACEMENT_DETAILED_BALANCE_CONTRACT.md`, grounded in the two primary
papers attached after the initial publication.

## Intake and provenance

The user requested native Lean 4 / Mathlib compilation and an upstream draft PR.
The latest source text was:

> carnot cycle of information the expansion and contraction the weyl gauge scale (the gromov witten theory and volume) thermodynamic partition function renormalization to the unitary equilibrium soureau leflet of constant entrpy for the metriplectiv system renormalization of the bloch ball of the spacetime fromt of sorts radial breatehr carnot cycke changing entropy around the equilibrium leaf the piston is in the radial direction tie lg time weyl gauge orthogonal to unitary evolution of sorts information thermodynakic canrnot cycle entropy and surface orbits time psiton goldstone bosons the codebase has some of these ideas partially interconnected however strange they may seem wilson loops ness ireversible and reversible oscvillations around the equilibrium forward and backward waves with reflection causal wave front waves

Earlier context asked about Fourier/Mellin phase and scale, Clifford/Dirac
operators, split octonions, and the
[OpenAI lattice Standard Model article](https://openai.com/index/step-toward-defining-the-standard-model/).
Those topics motivate the work; they are not assumptions implying the operator
results below. The lattice and determinant-line work remains in separate PRs.

## Corrected claim ledger

| Intake structure | Exact mathematical meaning | Disposition |
| --- | --- | --- |
| Common Weyl scale of a positive weight | $P\mapsto cP$, followed by $P/\operatorname{Tr}P$, $c>0$ | Existing native normalized density is unchanged; this cannot itself be a radial entropy change. |
| Unitary entropy leaf | $\rho\mapsto U\rho U^*$ | Existing actual matrix entropy is invariant for strictly positive inputs. Each orbit lies in an entropy level; the converse is not asserted. |
| Radial relaxation | $R_\sigma(X)=\operatorname{Tr}(X)\sigma$, $\Phi_\lambda=\lambda\,\mathrm{id}+(1-\lambda)R_\sigma$ | Constructed full-matrix linear-map bridge, with explicit normalization and positivity hypotheses. |
| Compatibility with rotation | Commutator of the inner derivation $\operatorname{ad}_K$ and $R_\sigma$ or $\Phi_\lambda$ | Exact defect retained; zero follows when $[K,\sigma]=0$. |
| Radial/orbit orthogonality | $\operatorname{Tr}((\rho-\sigma)[K,\rho])=\operatorname{Tr}([K,\sigma]\rho)$ | Full ordered matrix identity. Star-trace orthogonality additionally uses Hermitian input and reference. |
| Thermal equilibrium target | Existing CFC Gibbs density $\sigma_\beta=e^{-\beta H}/Z_\beta$ | Native commutation with $H$ discharges stationarity for the physical skew generator $K=-iH$. |
| Expansion/contraction cycle | Two relaxation steps with one normalized target | A return outside the target is impossible if the parameter product differs from one. A driven engine must supply changing controls, targets, or additional operations. |
| Heat versus work | State change at fixed $H_0$, then switch $H_0\to H_1$ at fixed final state | Exact finite trace-energy identity; no unproved heat-path independence. |
| Closed metriplectic / GENERIC dynamics | Poisson part annihilates the entropy differential; dissipative part annihilates the energy differential | Not implied by replacement relaxation, which generally exchanges system energy with a bath. |
| NESS | Stationary system with nonzero resolved reservoir currents and entropy production | Requires reservoir decomposition; a stationary density alone is insufficient. |
| Carnot efficiency | A reversible two-temperature heat/work/entropy ledger | Not derived by channel identities. Four strokes, baths, controls, and reversible entropy exchange remain required. |
| Gromov–Witten volume, Wilson loops, Goldstone modes, causal reflected fronts | Distinct geometric, gauge, symmetry-breaking, and PDE structures | Open connecting maps and hypotheses; no identification by shared terminology. |

## Existing owners actually reused

All paths are relative to `lean/InfoGeometry/`.

| Owner | Actual declaration and hypotheses | Use |
| --- | --- | --- |
| `Quantum/ReplacementStateChannel.lean` | `replacement`; `replacement_trace` requires `trace σ = 1`; `replacement_completely_positive_all` requires PSD σ and quantifies every finite ancilla | Existing full matrix reset and its native complete positivity; no new reset definition or assumed CP field. |
| `OperatorAlgebra/LieJordanDuality.lean` | `ad ℂ K : Module.End ℂ Mat`, applied as $KX-XK$ | Native associative endomorphism composition of a noncommutative derivation. |
| `OperatorAlgebra/LieJordanTraceDuality.lean` | `trace_ad_skew`, cyclic trace identities | Reversible energy pairing and radial defect. |
| `Quantum/MatrixBoundaryPurification.lean` | Hermitian H; `normalizedGibbs`, `normalizedGibbs_posSemidef`, `normalizedGibbs_commute`; `trace_normalizedGibbs` also needs a nonempty index type | Actual CFC Gibbs target and stationary physical Hamiltonian consumer. |
| `Canonical/PolarFrameTraceDensity.lean` | `normalizedDensity_scale`, with strictly positive P, nonempty finite index, and positive real scale | Existing normalization-gauge boundary, not a new theorem in this PR. |
| `Canonical/MatrixEntropyUnitaryOrbit.lean` | `matrixEntropy_unitary_conjugate`, actual CFC logarithm, unitary U, strictly positive P | Existing entropy-orbit boundary; no replacement entropy monotonicity inferred. |

The search covered canonical `lean/`, the parallel `src/` lane, direct imports
and consumers, relevant thermodynamics/quantum/operator owners, and bounded
context preflight. Existing replacement consumers include finite history
recovery; normalized density is also consumed by BKM and operator
log-determinant geometry. The PR extends the canonical lane only. No live
graph-index freshness or exhaustive external-library coverage is claimed.

`FiniteEntropyLeaves` supplies generic level-set and trace statements, not by
itself von Neumann entropy invariance. `SouriauWeylPartitionBridge` concerns
a finite arithmetic Euler/Weyl denominator with a supplied compatibility
field; it does not replace the matrix Gibbs owner.
`SOURIAU_BOST_CONNES_TRANSITION_STATUS.md` records the separate analytic limits
of that construction. The existing two-dimensional radial/rotation example
in `LinShuKMSPetzRadialSynthesis` does not supply the full matrix bridge.

### Other existing scale, volume, and Souriau connections

The following existing owners were also inspected. They are source-audited
context, not additional imports or modules certified by this PR's focused
three-owner compiler receipt.

| Existing owner | Established source-level connection and boundary |
| --- | --- |
| `Physics/ZornScalingFlow.lean` | Reciprocal scaling on the complex Zorn carrier, composition quadratic-norm preservation, and sector exchange taking the scale parameter to its inverse. `zornScale_mul_iff_pow_six_eq_one` states that uniform scaling preserves Zorn multiplication exactly when the complex unit parameter satisfies $p^6=1$. The separate rank-two determinant-one torus action is multiplicative. |
| `Physics/YangBaxterZornBridge.lean` and `Physics/ZornBraidScalingCovariance.lean` | Native eight-dimensional left-multiplication matrices and braid operators. Arbitrary-unit similarity preserves trace, determinant, characteristic polynomial, and representation kernel. Identifying that similarity with left multiplication by the scaled Zorn element retains the $p^6=1$ hypothesis. |
| `Projective/SplitOctonions/ZornFlowRelativeVolume.lean` | Determinant-ratio composition with nonzero denominator hypotheses, scalar-scale factors, and log-barrier shifts under explicit positivity and similitude assumptions. The total relative-density expression takes an external Jacobian as data; it does not construct a smooth change-of-variables theorem. |
| `Lie/CanonicalZornG2CartanSouriauCharacterBridge.lean` and `Lie/CanonicalZornG2FiniteGibbsTomitaBridge.lean` | A finite nonempty state space with a rank-two moment-map datum, normalized real Gibbs weights, and Massieu/Fisher identities. The Gibbs-mean operator is a scalar multiple of the identity on the real doubled Hilbert space; it is distinct from the CFC matrix Gibbs density used here. |
| `Lie/CanonicalZornG2NativeWeylMellinBridge.lean` | Finite Weyl-symmetrized character sums transported to the native Cartan, with short- and long-generator reflection invariance. This does not identify a Weyl-group reflection with a Weyl metric-scale gauge. |

These owners establish existing portions of the requested scale, volume, and
thermodynamic connections. None supplies the full-matrix replacement
semigroup, its arbitrary-finite-ancilla complete positivity, the Hamiltonian
commutator defect, and the CFC Gibbs consumer proved together in this PR.

## Carrier and conventions

Let $\mathrm{Mat}=M_n(\mathbb C)$, represented by native
`Matrix (Fin n) (Fin n) ℂ`. Matrix products are ordered. Inputs are not
assumed diagonal and do not generally commute. The maps live in
`Module.End ℂ Mat`; its product is composition.

The existing replacement map and the new relaxation family are

$$
R_\sigma(X)=\operatorname{Tr}(X)\sigma,\qquad
\Phi_\lambda=\lambda\,\mathrm{id}+(1-\lambda)R_\sigma.
$$

For $\operatorname{Tr}\sigma=1$, replacement is idempotent. Algebraic identities
allow complex $\lambda$. Channel statements use real $0\leq\lambda\leq1$,
positive semidefinite $\sigma$, and trace one for trace preservation.
Complete positivity is proved at every finite ancillary matrix size using
the existing amplification API. Normalization and positivity remain separate
hypotheses.

## New dependency order

1. Existing replacement map and its arbitrary finite amplification theorem.
2. Replacement idempotence, relaxation, composition, centered action,
   positive cone preservation, and complete positivity.
3. Existing inner derivation, its exact commutator defect with replacement
   and relaxation, and cyclic trace pairing.
4. Trace preservation and energy bookkeeping for the combined generator.
5. Actual Gibbs density supplying a compatible stationary target.

These are implemented maps and implications. Entropy geometry, spacetime,
gauge holonomy, and Gromov–Witten theory are not added as implied edges.

## Operator statements

For a normalized target,

$$
R_\sigma^2=R_\sigma,\qquad
\Phi_\lambda\Phi_\mu=\Phi_{\lambda\mu},\qquad
\operatorname{Tr}(\Phi_\lambda X)=\operatorname{Tr}X.
$$

For arbitrary matrices,

$$
\Phi_\lambda X-R_\sigma X=\lambda(X-R_\sigma X).
$$

Consequently, if $\lambda\mu\ne1$ and
$\Phi_\lambda(\Phi_\mu X)=X$, then $X=R_\sigma X$.
On the trace-one hyperplane this says $X=\sigma$.
This is a fixed-common-target result; it does not exclude driven cycles.

The exponential parameter gives an actual differentiable matrix path:

$$
\Phi_t=\Phi_{\exp(-\gamma t)},\qquad
\Phi_{s+t}=\Phi_s\circ\Phi_t,\qquad
\frac{d}{dt}\Phi_t(X)=\gamma(R_\sigma-\mathrm{id})(\Phi_t(X)).
$$

The semigroup and current-state generator identities use trace-one sigma.
For PSD sigma and nonnegative rate and time, the path is completely positive;
normalization additionally makes it trace preserving. The logarithmic
contraction parameter is $\log\lambda=-\gamma t$. This is a scale parameter of
the normalized-state relaxation, not a Weyl metric gauge identification.
No trajectory for the combined Hamiltonian-plus-relaxation operator is
constructed in this PR.

The commutator defect is

$$
[\operatorname{ad}_K,R_\sigma]X=\operatorname{Tr}(X)[K,\sigma],\qquad
[\operatorname{ad}_K,\Phi_\lambda]X
=(1-\lambda)\operatorname{Tr}(X)[K,\sigma].
$$

For a normalized target, $[\operatorname{ad}_K,R_\sigma]=0$
is equivalent to $[K,\sigma]=0$.

Radial displacement obeys

$$
\operatorname{Tr}((\rho-\sigma)[K,\rho])
=\operatorname{Tr}([K,\sigma]\rho).
$$

When $[K,\sigma]=0$, the right side vanishes. For Hermitian $\rho,\sigma$,
this also gives zero in the star-trace pairing. Interpreting $[K,\rho]$ as
a unitary-orbit tangent requires skew-adjoint $K$. Orthogonality to one
compatible tangent is not orthogonality to every unitary tangent for an
arbitrary reference state.

The combined linear operator is

$$
\mathcal G_{K,\sigma,\gamma}
=\operatorname{ad}_K+\gamma(R_\sigma-\mathrm{id}).
$$

Its definition permits every real $\gamma$; physical relaxation uses
nonnegative rates. For $[K,H]=0$ and $\operatorname{Tr}\rho=1$,

$$
\operatorname{Re}\operatorname{Tr}(H\mathcal G\rho)
=\gamma\bigl(
\operatorname{Re}\operatorname{Tr}(H\sigma)
-\operatorname{Re}\operatorname{Tr}(H\rho)\bigr).
$$

The Gibbs consumer uses the convention $\hbar=1$, sets $K=-iH$,
and takes $\sigma=\sigma_\beta$.
Native functional-calculus commutation supplies stationarity. Raw
$\operatorname{ad}_H$ is not called physical Hermitian-state evolution.
Define $E_H(A)=\operatorname{Re}\operatorname{Tr}(HA)$.
For real $\lambda$ and $\operatorname{Tr}\rho=1$, the finite-step energy
change is also computed before taking a rate:

$$
E_H(\Phi_\lambda\rho)-E_H(\rho)
=(1-\lambda)\bigl(E_H(\sigma)-E_H(\rho)\bigr).
$$

For externally changed controls,

$$
\operatorname{Tr}(H_1\rho_1)-\operatorname{Tr}(H_0\rho_0)
=\operatorname{Tr}(H_0(\rho_1-\rho_0))
+\operatorname{Tr}((H_1-H_0)\rho_1).
$$

This is exact for arbitrary ordered matrices and describes a specified
two-stage convention. A general simultaneous stroke requires a path and
its differential/integral heat-work ledger.

## Thermodynamic interpretation and open obligations

A scalar rescaling of an unnormalized weight cancels on normalization.
Scaling a Hamiltonian at fixed inverse temperature changes $\beta H$.
Scaling $H\mapsto aH$ and $\beta\mapsto\beta/a$, $a>0$, instead keeps that
product fixed. These are distinct operations. A Weyl metric gauge
transformation needs its own geometric owner.

A qubit has a Bloch-ball description. Unitary conjugation preserves its
spectrum and radius; a suitable channel can change its radius. This does not
identify the Bloch ball with relativistic spacetime. In higher dimension an
entropy level generally contains multiple unitary orbits.

Gibbs-target relaxation need not increase system entropy. For example,
$\rho=I_2/2$ has entropy $\log2$, whereas the full-rank Gibbs target
$\sigma=\mathrm{diag}(3/4,1/4)$ for
$H=\mathrm{diag}(0,\log3)$ and $\beta=1$ has smaller entropy
$2\log2-\tfrac34\log3$. This is an explanatory calculation, not an added
Lean entropy theorem. Relative entropy/free energy or total
system-plus-reservoir entropy needs its own proof.

For closed GENERIC, the degeneracy conditions are $J\,dS=0$ and $M\,dE=0$,
with a positive semidefinite dissipative operator. The energy balance above
shows why an open replacement bath does not automatically give that closed
structure. Reservoir state and energy variables are needed.

A reversible Carnot cycle additionally needs two bath temperatures, controlled
Hamiltonians, and reversible entropy exchange. With positive entropy transfer
$\Delta S$, temperatures $T_h>T_c>0$, and justified reversible relations

$$
Q_h=T_h\Delta S,\qquad Q_{c,\mathrm{out}}=T_c\Delta S,
$$

these formulas use $k_B=1$ when entropy is the dimensionless matrix entropy;
otherwise $\Delta S$ denotes physical entropy.

Energy balance yields $W_{\mathrm{out}}=Q_h-Q_{c,\mathrm{out}}$ and
$\eta=1-T_c/T_h$. The constitutive and reversible relations are not derived
from the replacement-channel identities. No complete Carnot engine,
system-entropy monotonicity, relative-entropy contraction, thermodynamic
limit, or closed GENERIC bracket is claimed.

NESS needs separate reservoir currents even when the system density is
stationary. Wilson holonomy requires a connection and loop transport;
Goldstone conclusions require symmetry and breaking hypotheses; causal
fronts require a hyperbolic PDE and characteristic geometry; Gromov–Witten
invariants require the relevant symplectic/moduli-space construction.
These are explicit next obligations.

## Primary references

- Mittnenzweig and Mielke,
  [An entropic gradient structure for Lindblad equations and couplings of quantum systems to macroscopic models](https://arxiv.org/html/1609.05765v3):
  relative entropy/free energy, detailed balance, and the quantum-plus-reservoir
  GENERIC distinction.
- Mielke,
  [Dissipative quantum mechanics using GENERIC](https://www.wias-berlin.de/preprint/1710/wias_preprints_1710.pdf):
  degeneracy conditions and closed versus open energy/entropy balance.
- Marle,
  [On Gibbs states of mechanical systems with symmetries](https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf):
  moment-map Gibbs measures, normalization shifts, and thermodynamic Legendre
  relations.

References delimit interpretation. Lean acceptance depends on exact source,
scoped compiler output, and native axiom audit in the accompanying review.
