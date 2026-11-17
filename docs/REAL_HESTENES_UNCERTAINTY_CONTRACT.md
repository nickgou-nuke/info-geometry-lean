# Real Hestenes observable uncertainty

## Intake and repository context

This change expands the existing operatorial uncertainty development using
real Hilbert operators and the native even spacetime Clifford algebra. It
builds on the existing phase-observable owners in upstream
[PR #372](https://github.com/nickgou-nuke/info-geometry-lean/pull/372), at
revision `0953827c47dafa198b2ab442b585719cc2ecd9c8`. The PR is stacked on
`formalize/fourier-dirac-covariance-bridges`; that dependency remains a draft.

The original attachment is preserved byte for byte in
[`intake/2026-11-17-real-hestenes-uncertainty.txt`](intake/2026-11-17-real-hestenes-uncertainty.txt).
Its SHA256 is
`23fefb194cbc62858b22b43be8f4a915f3d0e89656e6fac6a0a0276e6770342e`.
The supplied text ends mid-sentence; no missing continuation has been inferred.
The subsequent user instruction selects the existing real Hestenes/Krein
operatorial uncertainty code as the implementation context.

The source search included declarations, alternate formulations, actual import
dependencies, consumers, the `lean/` and `src/` trees, and the changed-file
inventories of open PRs #357–375. The initial main-based candidate was
reconciled when PR #372's canonical phase/commutator owners appeared. Their
existing public APIs are retained; this change generalizes their actual proofs
to arbitrary real geometric phases and adds the native Hestenes specialization.
PR #375's complex QGT matrix and real Fourier work is not a dependency.

## Existing owner map

| Owner | Reused result or relevant background | Actual scope |
|---|---|---|
| `Krein/InternalPhaseGram.lean` | The existing real Bessel area proof | Generalized to norm-preserving, self-orthogonal real phase operators without adding completeness to the canonical API |
| `Krein/PhaseLinearObservableCommutator.lean` | `centeredVector`, arbitrary-shift cancellation, actual commutator identities | Generalized to skew phase pairing and observable/phase commutation; existing finite-family commutator mixing retained |
| `Canonical/PhaseObservableUncertainty.lean` | Centered Robertson–Schrödinger and Robertson bounds; normalized second-moment identity | Existing canonical bounds preserved as specializations of the geometric-phase bounds |
| `Canonical/OperatorialUncertainty.lean` | Historical area-bound API and channel uncertainty | Unchanged forwarding owner on the positive real doubled Hilbert carrier |
| `Canonical/OperatorialCramerRao.lean` | Channel metric, Cauchy–Schwarz and unit-response bounds | Uncentered channel Gram geometry |
| `Canonical/HestenesModularBregman.lean` | `hilbertExpectationAt` | The existing real positive-Hilbert state/operator pairing |
| `Canonical/BogoliubovTransport.lean` | `transportCommutator`, `IsPhaseLinear` | Actual bounded-operator composition difference and canonical phase commutation |
| `Canonical/OperatorDictionary.lean` | `phaseAxisK`, its square and skew pairing | Internal real `Jε`, not an external complex scalar |
| `Geometry/RealHamiltonianMoment.lean` | `inner_map_left`, `inner_map_map` | Skew pairing and isometry from a real skew-adjoint square root of `-Id` |
| `Canonical/HestenesClPlus14.lean` | `ClPlus14`, `gamma`, `sigmaEven` | Native Mathlib even Clifford algebra with signature `(+---)` |
| `proofs/HestenesQuaternionCore.lean` | `q₃_sq`, `adjoint_q₃` | Native even-Clifford rotation generator and its Hermitian adjoint |
| `Canonical/HestenesHermitianMatrixBridge.lean` | `clPlusToPauli_hestenesAdjoint` | Compatibility of native Hestenes adjunction with an existing faithful representation |
| `Canonical/Cl11GNSRealDoubledKreinBridge.lean` | Real doubled readout and left/right bounded actions | Real coordinate representation, positive Hilbert pairing and commuting left/right actions |
| `Krein/BornRuleCore.lean` | Background: fundamental-symmetry/Hilbert pairing identities | Explains the positive pairing; this file is not imported by the new uncertainty owner |

`Canonical/HestenesQuaternionCore.lean` is a different octonion-slice owner.
It is not a substitute for the native spacetime-algebra owner under `proofs/`.
Likewise, the Cl(1,1) pseudoscalar in `Clifford/Hestenes.lean` squares to `+1`;
it cannot replace the square-minus-one phase in this uncertainty inequality.

## Claim classification

| Claim or proposed inference | Classification | Treatment |
|---|---|---|
| Quantum uncertainty requires external complex scalars | Refuted by existing source | Reuse the real doubled operatorial owner |
| A geometric phase may replace scalar imaginary notation | Locally provable with explicit carrier | Use a real skew-adjoint operator whose square is `-Id` |
| Hestenes right multiplication is the same as canonical `Jε` | Not assumed | They instantiate the same theorem separately; no equality is claimed |
| Observable uncertainty should involve the actual commutator | Locally provable | Center bounded self-adjoint operators and derive the phase-twisted commutator coefficient |
| Indefinite Krein variance is automatically positive | False | Use the positive Hilbert pairing; retain the existing signed modular variance separately |
| Noncommuting left observables must commute with each other | False | They commute with the right phase; their mutual commutator is retained |
| All real matrix quantum Cramér–Rao infrastructure is absent | Refuted by existing source | Existing `Quantum/QuantumCramerRaoBound.lean` is retained |
| Fourier, Legendre and Penrose transforms are one involution | Unsupported as stated | No transform-identification theorem is introduced |
| A semiclassical limit automatically yields convex Legendre duality | Requires analytic/model hypotheses | Outside this bounded-operator change |
| A general covariant POVM achieves every multiparameter bound | Requires statistical and attainability hypotheses | Outside this change |
| Full Lichnerowicz, SUSY and positive-energy time-operator conclusions follow | Not consequences of these algebraic lemmas | No such conclusion is promoted |

## Exact observable contract

Let `H₂ = DoubledSpace E`, with `E` a complete real inner-product space, and
let `A`, `B`, `P` be bounded real linear endomorphisms of `H₂`.

The existing expectation and new centered quantities are

\[
\mu_\psi(A)=\langle\psi,A\psi\rangle_{\mathbb R},\qquad
A_0=A-\mu_\psi(A)\operatorname{Id},
\]

\[
V_\psi(A)=\|A_0\psi\|^2,\qquad
C_\psi(A,B)=\langle A_0\psi,B_0\psi\rangle_{\mathbb R},\qquad
c^P_\psi(A,B)=\langle P\psi,(AB-BA)\psi\rangle_{\mathbb R}.
\]

For Hilbert-self-adjoint `A`, `B`, with `AP = PA`, `BP = PB` and `P* = -P`,
the exact sign convention is

\[
c^P_\psi(A,B)=2\langle P(A_0\psi),B_0\psi\rangle_{\mathbb R}.
\]

The ordinary real expectation of `AB - BA` is zero for self-adjoint `A`, `B`.
The insertion of the real geometric phase in `c` is therefore substantive.
Subtracting real multiples of the identity leaves the full operator
commutator unchanged, before any scalar readout.

Adding `P² = -Id` gives the area bound

\[
C_\psi(A,B)^2+\frac{c^P_\psi(A,B)^2}{4}
\le V_\psi(A)V_\psi(B).
\]

The inequality holds for every `ψ` with the explicitly defined centered norms.
The usual statistical interpretation uses `‖ψ‖ = 1`. Under that hypothesis,
the centered mean is zero and

\[
V_\psi(A)=\langle\psi,A^2\psi\rangle_{\mathbb R}-\mu_\psi(A)^2.
\]

Normalization is required in those moment identities, not silently assumed in
all preceding lemmas. Self-adjointness always means adjunction for the
positive Hilbert pairing. A raw Krein-self-adjointness hypothesis would not
suffice.

## Native Hestenes specialization

The geometric carrier is the existing `ClPlus14`, the native even algebra of
`Cl(1,3)`. The phase is right multiplication by the existing
`HestenesQuaternionCore.q₃`, transported to the existing real doubled
Hilbert–Schmidt carrier. Observables act by left multiplication.

The bridge must construct, rather than assume, the following facts:

1. The native generator is the real spatial bivector and has square `-1`.
2. Its right action has square `-Id` and Hilbert adjoint equal to its negative.
3. Every left action commutes with that right action by associativity.
4. Hestenes-Hermitian elements give Hilbert-self-adjoint left actions.
5. The left action preserves multiplication faithfully, retaining genuine
   noncommutative observable products.
6. The centered bound follows by substituting those proved facts into the
   general real operator theorem.

The existing Pauli representation is reused internally to prove the bridge.
Public geometric inputs and the uncertainty readout are real. This does not
claim to remove complex-coordinate modules elsewhere in the repository or to
identify every right phase with the central canonical phase.

The concrete sharp example uses the native Clifford unit, whose squared
Hilbert–Schmidt norm is `2`. For the left actions of `sigmaEven 0` and
`sigmaEven 1`, the target readouts are zero means, variances `2`,
zero covariance, and a phase-twisted commutator coefficient `4`. Its target
identity is `0² + 4² / 4 = 2 * 2`. This is an unnormalized geometric example;
it is not presented as a unit-state second-moment identity.

## Mathematical dependency order

| Prerequisite | Consumer | Mathematical edge |
|---|---|---|
| Phase norm preservation and self-orthogonality | Real area bound | An orthonormal two-plane and the existing Bessel proof |
| Phase square and skew adjoint | Geometric phase hypotheses | Derive isometry and skew pairing in the complete Hilbert setting |
| Existing expectation | Centered observables | Subtraction of the real mean times identity |
| Self-adjointness and phase commutation | Twisted commutator readout | Move each operator across the real inner product |
| Centering | Covariance and variance | Apply the existing Hilbert geometry to actual observable deviations |
| Area bound and commutator identity | Robertson–Schrödinger inequality | Substitute the computed phase coefficient |
| Native Clifford and adjoint compatibility | Hestenes specialization | Construct a concrete geometric phase and observable representation |

These are the dependencies represented by the proof scripts. The acceptance
record below distinguishes source review from completed kernel checking. The
attachment's philosophical labels do not create additional formal implications.

## Acceptance record

Implementation and independent review are in progress. This section is updated
only from completed kernel, axiom, semantic and integration checks on the exact
published source. A source review is not a compiler certificate, and a scoped
module build is not a whole-repository build.
