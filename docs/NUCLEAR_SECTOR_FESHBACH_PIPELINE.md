# Symmetry-resolved nuclear configuration mixing

## Intake and provenance

This extension continues PR #220 from `e21e2fec860ba3b2b03ff9fbfb2791a2a1518634`.
The requested dependency order is sector projectors, transition selection,
exact Feshbach reduction, consistently transported observables and norms, and
joint energy/transition/transfer identifiability. The supplied sulfur-37
spin/parity labels are treated as model inputs, not experimental conclusions.

The physical reference supplied with the task is
<https://arxiv.org/abs/nucl-th/0504042>. The formal claims below are independent
algebraic and Hilbert-space statements; their proof authority is Lean.

## Ground-truth theorem contracts

### Chosen symmetry sectors

Use native `Module.End`, `LinearMap`, and `Submodule` on a chosen product of
sector spaces. Configuration multiplicity is retained inside each sector.
Construct mutually disjoint idempotent sector projections and a finite
resolution of the identity. If initial/final spectral projectors and a
rectangular operator satisfy

`Si Pi = λi Pi`, `Pf Sf = λf Pf`, `Sf O = η O Si`,

then prove `Pf O Pi = 0` whenever `λf ≠ η λi`. A commuting Hamiltonian is the
case `η = 1`. The physical identification of the supplied spectral operators
with `J²` and spatial parity remains explicit. Scalar `J(J+1)` alone does not
construct a many-body spin representation.

The doubled-spin triangle inequalities and electromagnetic parity characters
form a necessary-support predicate. Compatibility of the supplied labels with
E2, and incompatibility with M1, do not prove a nonzero E2 matrix element or a
full Wigner--Eckart theorem. Spatial parity, fermion parity, CAR grade, and the
model/complement split are separate objects.

### Exact projector reduction

Carrier: `Module.End K V`, for a scalar field `K` and a `K`-module `V`.
For `P² = P`, set `Q = 1 - P` and `D(E) = E Q - Q H Q`.
An eliminated-space inverse `R` must satisfy

`Q R = R`, `R Q = R`, `R D = Q`, `D R = Q`.

Define `Heff = P H P + P H R H P` and `Ω = P + R H P`.
The exact claims of this layer are:

- `P Ω = P`;
- `H Ω - E Ω = Heff - E P`;
- for `P v = v`, `H (Ω v) = E Ω v` iff `Heff v = E v`;
- every full eigenvector is reconstructed by `Ω (P ψ) = ψ`;
- nonzero full eigenvectors have nonzero model projections.

The inverse is constructed from a native `LinearEquiv` on `ker P` whose
forward map is `E id - q H j`, where `q` is the corestriction of `Q` and `j`
is the subtype inclusion. Its existence is an explicit resolvent hypothesis;
no inverse of `D` on the full ambient space is asserted. The graph map is
injective only after restricting its domain to the model subspace.

Commutation with both `P` and `H` propagates to the complementary resolvent,
wave operator, and effective Hamiltonian. With an explicit star structure,
self-adjoint `P`, `H`, and energy imply self-adjointness of the effective
Hamiltonian. Self-adjointness requires the displayed self-adjoint data;
symmetry propagation requires only the stated commutation and inverse
equations and also applies to oblique idempotents.

### Boundary of the actual countable algebraic carrier

The concrete readout bridge uses only `Q R = R` and `D R = Q`. It identifies
the eigen-equation on reconstructed graph states with the corrected matrix
`qpnmMatrix + modelMatrix (H * R * H)`. It does not assert that every full
eigenvector belongs to this graph.

There is a stronger, proved obstruction to a two-sided inverse on the existing
unrestricted product `ℕ → Fin 4 → Coefficient`. For nonzero coupling `g`, define

`a₀ = 1`, `a₁ = E/g`,

`aₙ₊₂ = ((E - omega*(n+1))*aₙ₊₁ - g*aₙ)/(g*(n+2))`.

The actual carrier admits the stream
`ψ n = ![scalarCoefficient (a n), 0, 0, 0]` without any summability condition.
The owner operators give `ψ ≠ 0`, `P ψ = 0`, and `H ψ = E • ψ`, at every real
`E`, independently of the quasiparticle energy. Therefore `D(E) ψ = 0` and
no operator can satisfy `R D(E) = Q`. A right inverse alone is not excluded.

This is an obstruction in the algebraic product, not a statement about the
spectrum of a self-adjoint Hilbert-space Hamiltonian. The generic two-sided
theorems apply when their native complementary inverse exists. Their physical
use requires a compatible finite realization or a specified analytic carrier
and operator domain; sector labels alone do not supply that inverse.

### Effective transition operators

For complete real or complex inner-product spaces, possibly different at
source and target, use native continuous linear embeddings `Ωi`, `Ωf` and an
observable `O`. Define `Oeff = Ωf† O Ωi` and `NΩ = Ω† Ω`. Prove the exact
matrix-element identity, positive semidefiniteness, and normalization by both
induced norm factors. The weight is strictly positive on nonzero vectors when
the wave map is injective. Symmetry transport uses explicit intertwining
equations and derives vanishing of incompatible projected effective blocks.

For a finite-dimensional Hilbert realization, the code restricts the actual
Feshbach wave map to `range P`, obtains continuity through mathlib, and proves
injectivity using `P Ω v = v`. The induced normalization theorems therefore
apply to a constructed embedding, not merely an assumed injective map.

This layer does not put a Hilbert norm on the existing algebraic product
`NuclearFiveGradeCommonCarrierRepresentation.Carrier`. Applying Hilbert-space
transition statements to that carrier requires an additional compatible
realization. A calibrated physical E2/M1 operator must also be supplied.

### Joint identifiability in the existing real two-state model

Reuse `NuclearConfigurationMixing.spectralHamiltonian`, `strength_mixed_final`,
and `SolovievTransitionStrength.amplitude`. With `c²+s²=1`, the calibrated
transfer weight `w=s²` fixes both diagonal mixing weights. A coherent strength
with known nonzero basis amplitudes `a,b` fixes `cs` through

`B = (1-w) a² + w b² + 2 cs a b`.

Together with the two spectral energies these observations determine the
matrix in the chosen configuration basis. The common sign of `(c,s)` is
redundant. Unknown calibration retains the existing non-identifiability
result; energy and transfer alone need not determine the off-diagonal sign.

## Existing owners and reuse boundaries

- `Physics/NuclearOperatorSchurComplement.lean` owns the associative Schur
  expression `E0 - V * Binv * W` and explicit two-sided inverse data.
- `Canonical/PhysicalBdGPairingBridge.lean` already proves a specialized
  continuous-linear spectral graph reduction. The present task extends the
  arbitrary-idempotent nuclear interface and does not replace that owner.
- `Physics/NuclearConfigurationOperatorLift.lean` owns the faithful corner
  lift and the exact model projection on the common five-grade carrier.
- `Physics/NuclearConfigurationGradedReadout.lean` proves the exact `P H P`
  readout and the obstruction from full-Hamiltonian phonon leakage.
- `Core/PeirceTangent.lean` already proves the off-diagonal tangent identity
  and its commutator characterization. Those results are reused directly.
- `SuperGrassmannian/GraphIdempotentDirections.lean` already provides the
  native two-Hom-space equivalence for algebraic projector directions.

## Explicit scope

No fitted sulfur-37 mixing fraction, many-body shell-model Hamiltonian,
physical supersymmetry, gravitational field, triaxial dynamics, full SU(2)
tensor-operator construction, or experimental lifetime extraction is claimed.
The code separates exact identities from supplied symmetry, inverse,
calibration, and physical-representation hypotheses.

## Entry point and theorem owners

Import `InfoGeometry.Physics.NuclearConfigurationInference` for the complete
extension. Its focused owners are:

- `NuclearSymmetrySectors`: actual chosen projectors, spectral block selection,
  distinct spatial parity, and explicitly bounded E2/M1 support predicates.
- `NuclearFeshbachReduction`: operator residual identity and exact two-way
  reconstruction of eigen-equations on the model space.
- `NuclearComplementaryResolvent`: native inverse on `ker P`, with all four
  ambient support/inverse laws derived.
- `NuclearFeshbachSymmetry`: conserved symmetries and self-adjointness under
  elimination, with the necessary hypotheses.
- `NuclearFeshbachConfigurationBridge`: the actual common-carrier readout is
  `qpnmMatrix + modelMatrix (H * R * H)`, and this corrected matrix governs
  the reconstructed graph eigen-equation under right-inverse hypotheses.
- `NuclearAlgebraicResolventObstruction`: an explicit discarded eigenvector
  at every real energy excludes a left complementary inverse on the actual
  unrestricted common carrier when the phonon coupling is nonzero.
- `NuclearEffectiveObservables`: distinct source/target adjoint sandwiches,
  induced Gram operators, and exactly normalized amplitudes and strengths.
- `NuclearFiniteEffectiveModel`: native finite Hilbert restriction of the
  Feshbach wave operator to its model domain.
- `NuclearEffectiveSelection`: ambient covariance implies vanishing of
  forbidden dressed transition blocks, including the E2/M1 parity character.
- `NuclearJointIdentifiability`: calibrated joint identification of the
  existing two-state Hamiltonian and an explicit energy/transfer ambiguity.

## Verification

`[kernel_verified]`: 103 new theorem declarations and 22 named definitions
across 11 Lean modules, including the umbrella import.

The repository pins Lean `4.34.1` and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The toolchain, manifest, and
package configuration are unchanged.

- The targeted locked build
  `lake build InfoGeometry.Physics.NuclearConfigurationInference` succeeds
  (8977 jobs, including cached dependencies). It uses an isolated Lake project
  whose `InfoGeometry` and `DAG` libraries point to the actual repository
  source directory and whose mathlib checkout is exactly the pinned revision.
  The dependency cache is a physical copy, with no symlinked package roots.
- A fresh independent QA agent repeated that build, then directly elaborated
  exact-byte copies of all 11 new Lean files with `lake env lean`, sequentially
  under the repository's native shared build lock. All exit codes are zero;
  all 11 direct-source diagnostic logs are empty.
- A separate `#print axioms` probe covers all 125 named definitions and
  theorems, with no missing, extra, or duplicate symbols. Its axiom union is
  exactly `propext`, `Classical.choice`, and `Quot.sound`. No custom axioms
  or `sorryAx` occur.
- The placeholder scan, staged proof-proxy gate, OpenGauss screener,
  `refute --strict`, static `review --gate GATE_4`, semantic-vacuity gate,
  and whitespace check pass. The screener reports no violations; strict
  refutation reports 11 passes. Static review is supplemented by the separate
  Lean checks above.
- The semantic-vacuity gate emits 13 lexical `trivial_surface` warnings:
  `coefficient_zero`, `coefficient_one`, `coefficient_step`,
  `coe_kerProjection`, `liftInverse_apply`, `normMetric_adjoint`,
  `effectiveOperator_adjoint`, `modelMatrix_add`,
  `waveOperator_mul_projection`, `waveEmbedding_apply`,
  `spectralHamiltonian_global_sign`, `sectorProjector_apply`, and
  `sectorSymmetry_apply`. Independent source review classifies these as
  native evaluation, recurrence, or short algebraic laws, with no circularity
  or unsupported physical claim.
- Authoring, mathematical A-A review, and acceptance QA used separate agents.
  The frozen source hashes remained identical throughout independent QA.
  New modules are warning-free; inherited dependency warnings remain.

The prescribed repository-root locked build was also retried. It stops before
target compilation because `external_refs/atlas-lean` is absent. The isolated
build verifies this complete source dependency graph; it does not certify a
whole-repository build or CI result. No replacement Atlas package or dependency
pin changes are introduced.

### Checked Lean source hashes

| File | SHA-256 |
| --- | --- |
| `NuclearAlgebraicResolventObstruction.lean` | `b79702cb9686e786e32be918c9da5611605471f456e1ee68ac75f18e95a06ea5` |
| `NuclearComplementaryResolvent.lean` | `3ef9b979793eff7a73b4a32f55992f95630cd4a72c7b5eea5e2552d832693798` |
| `NuclearConfigurationInference.lean` | `74b92ac4fe137a293f6ba2195e28c01c1e8a25b827fb0fbad01256b7de38fe96` |
| `NuclearEffectiveObservables.lean` | `ec875dbdfbb598c561c9affab1aa041bbd1fe2a68e2ab0bde167b1db5a35394b` |
| `NuclearEffectiveSelection.lean` | `846e3bb769075cd97bae65a5d1c203a1fc40c6246c2913441910384852bcbf1b` |
| `NuclearFeshbachConfigurationBridge.lean` | `3d1230d80e623a3864b29d6df4c8f8c99cbea83b5ef3abf55465ccfe8ce18f58` |
| `NuclearFeshbachReduction.lean` | `cedc3d9a3eeb0f6462739499c49a454af10fa94a24f145facae627e0f4db75ce` |
| `NuclearFeshbachSymmetry.lean` | `663c3a6bf6b96b85ad006836a4f3eb6e6da2b807910ec8d8aa0c41d26f7e0f86` |
| `NuclearFiniteEffectiveModel.lean` | `16939f566322784d1c449f1a3beb47e32b63083443d2fe4ff4f4d4559dd25d84` |
| `NuclearJointIdentifiability.lean` | `f78958e8e3e2a5d1c2e72819a46d673cf37288fd91ca3b43408bbf6388c79d28` |
| `NuclearSymmetrySectors.lean` | `ade96929c616a972f5c2e6894f10734e1d307574b792c4cd49e2cb030cd381c3` |
