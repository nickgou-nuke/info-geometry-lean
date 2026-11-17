# Native Hestenes spectral corners and related uncertainty owners

Date: 2026-11-17. Status: independently reviewed source and passing scoped source checks for the two selected owners. Native compilation and declaration-axiom acceptance are pending. The mathematical statements below describe the candidate declarations; this document is not a compiler certificate.

## Input provenance and mathematical interpretation

The four supplied texts are retained byte-for-byte as research input. Their psychological language, asserted deductions, and physical interpretations are not assumptions of the Lean development.

| Input | Preserved file under `docs/sources/` | SHA-256 |
|---|---|---|
| `Pasted text(20261117-081809).txt` | [hestenes_spectral_intake_20261117_01.txt](sources/hestenes_spectral_intake_20261117_01.txt) | `7bc043ed20e358d5afd85a4477c3c2cbadcdbd3a9c3f4d8ae4ad7750d41b39a3` |
| `Pasted text (2)(6).txt` | [hestenes_spectral_intake_20261117_02.txt](sources/hestenes_spectral_intake_20261117_02.txt) | `a491023d36718e9f034c8a5975c01d35c01e14ce0346e398caefc1e8d52cc802` |
| `Pasted text (3)(3).txt` | [hestenes_spectral_intake_20261117_03.txt](sources/hestenes_spectral_intake_20261117_03.txt) | `29e63c7500aaca938b4f3944867da88d10732da430e8219a5697981d42fa53ed` |
| `Pasted text (4)(1).txt` | [hestenes_spectral_intake_20261117_04.txt](sources/hestenes_spectral_intake_20261117_04.txt) | `b9de16352e57d99545684be35d91d935df030bc68a57849584caaff133edede0` |

Repository baseline: `08c34e03f610b452e03422037949196dc7d92d6d`. The unchanged environment pins are Lean `v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The recurring motifs admit precise mathematical counterparts, but the counterparts require their own definitions and proofs:

| Motif in the input | Precise mathematical object | Dependency that must be established first |
|---|---|---|
| Opposed sectors and complementarity | Complementary spectral idempotents `(1 ± β)/2` | The actual Clifford relation `β² = 1` |
| Projection and return | Ordered corner compression `P₊ x P₋` | Idempotence, orthogonality, and the chosen multiplication algebra |
| Reversal and reciprocal action | Clifford reversion or the fixed-observer adjoint | Each operation's action on projectors and reversal of product order |
| Tension between observables | The ordered commutator `AB − BA` | The actual bounded operators, self-adjointness, and phase-linearity |
| A bound joining two responses | A real Robertson–Schrödinger inequality | A positive inner product, internal orthogonal phase structure, and the commutator readout |
| Obstruction to an asserted synthesis | A nonzero native Clifford counterexample | A constructed witness and a proof that it is nonzero |

The present change publishes the native spectral-corner development. The uncertainty interfaces are already proposed in the related draft PRs below and are reused by reference. No duplicate uncertainty owner or competing extraction is added here.

## 1. Reuse of the existing uncertainty proposals

Remote source inspection found that the real operator part of these inputs is already covered by open draft [PR #372](https://github.com/nickgou-nuke/info-geometry-lean/pull/372) and its stacked [PR #379](https://github.com/nickgou-nuke/info-geometry-lean/pull/379). They have not been merged into the baseline. Their native acceptance is not certified by this change.

| Exact source inspected | Relevant declarations and scope |
|---|---|
| [PR #372: PhaseLinearObservableCommutator](https://github.com/nickgou-nuke/info-geometry-lean/blob/fd4a9f929a99b17adaeb6f8a3d2aa78141285324/lean/InfoGeometry/Krein/PhaseLinearObservableCommutator.lean) | `twice_centered_phase_pair_eq_commutator`, on full bounded real operators acting on `DoubledSpace`, with native Hilbert self-adjointness and commutation with `complex_i` |
| [PR #372: PhaseObservableUncertainty](https://github.com/nickgou-nuke/info-geometry-lean/blob/fd4a9f929a99b17adaeb6f8a3d2aa78141285324/lean/InfoGeometry/Canonical/PhaseObservableUncertainty.lean) | `centered_robertson_schrodinger`, `centered_robertson`, and normalized second-moment variance |
| [PR #379: CenteredOperatorialUncertainty](https://github.com/nickgou-nuke/info-geometry-lean/blob/2f52bb9cba2a45b316c4d65e8e5971cc78532e4a/lean/InfoGeometry/Canonical/CenteredOperatorialUncertainty.lean) | Scalar-shift commutator, centered self-adjointness/phase-linearity, covariance/anticommutator and normalized variance interfaces |
| [PR #379: HestenesRightPhaseUncertainty](https://github.com/nickgou-nuke/info-geometry-lean/blob/2f52bb9cba2a45b316c4d65e8e5971cc78532e4a/lean/InfoGeometry/Canonical/HestenesRightPhaseUncertainty.lean) | Proposed actual native readout, left observable and right phase `R(γ₂γ₁)`, their adjoint/action identities, and a sharp noncommuting example |

For `x=(A-aI)ψ`, `y=(B-bI)ψ`, their centered real operator contract includes

\[
2\langle Kx,y\rangle=\langle K\psi,(AB-BA)\psi\rangle,
\qquad
\langle x,y\rangle^2+\tfrac14\langle K\psi,(AB-BA)\psi\rangle^2
\leq\|x\|^2\|y\|^2.
\]

The arbitrary-center formula does not require a unit state. The ordinary second-moment variance and mean-centered covariance formulas require the stated normalization. The operators commute with the chosen phase; they need not commute with each other. The positive Hilbert pairing remains distinct from the indefinite Krein pairing.

The causal order is phase geometry and Bessel inequality → literal ordered-commutator readout → centered uncertainty → normalized statistical readouts. PR #372 already extracts the lower-level Gram proof, and PR #379 extends the native right-phase interface. An independently prepared overlapping uncertainty candidate was therefore not promoted in this publication.

[PR #380](https://github.com/nickgou-nuke/info-geometry-lean/pull/380) separately proposes native real spinor coordinates, observer pairings and a time-projector ideal. Its [RealSpacetimeObserver owner](https://github.com/nickgou-nuke/info-geometry-lean/blob/616c1854c2a68f913d510d5143cb080e93f53137/lean/InfoGeometry/Clifford/RealSpacetimeObserver.lean) includes `current_time_eq_observer`, identifying the actual scalar readout of `x γ₀ reverse(x) γ₀` with its positive observer form, plus nonnegativity and strict-positivity declarations. It remains an unmerged draft. Its time projector `(1+γ₀)/2` in the full Clifford algebra differs from the even boost projectors below. Baseline-only absence findings must not be mistaken for an assertion that these newer proposals do not exist.

## 2. Native spacetime spectral projectors and corners

Owner: [HestenesSpectralCorners.lean](../lean/InfoGeometry/Canonical/HestenesSpectralCorners.lean), namespace `HestenesSpectralCorners`.

### Actual algebra and conventions

The carrier is the full native Mathlib even Clifford algebra `HestenesCl14.ClPlus14 = CliffordAlgebra.even Q14`, with real signature `(+---)`. It retains all eight real dimensions and its noncommutative multiplication.

Choose `β = sigmaEven 0 = γ₁γ₀` and define

\[
P_+=\tfrac12(1+\beta),\qquad P_-=\tfrac12(1-\beta).
\]

This is the repository's canonical `β` axis. The supplied text sometimes chooses `γ₃γ₀` and reverses the `±` names. Those conventions are not silently identified here. The existing circular projectors also use the `sigmaEven 2` axis; the new definitions are not aliases of them.

The two operations are existing native owners:

- `reverseEven`: Clifford reversion, denoted `r` below.
- `hestenesAdjoint`: the fixed-observer operation `x ↦ γ₀ reverse(x) γ₀`, denoted `h` below.

The file introduces no competing `Star` instance and does not conflate bare reversion with a beta-twisted operation.

### Exact corner laws

The candidate proves both idempotence equations, both ordered orthogonality equations, and `P₊ + P₋ = 1`. Its involution and corner statements are:

| Operation | On projectors | On an arbitrary `(+,-)` corner |
|---|---|---|
| Reversion `r` | `r(P₊)=P₋`, `r(P₋)=P₊` | `r(P₊ x P₋)=P₊ r(x) P₋` |
| Fixed-observer adjoint `h` | `h(P₊)=P₊`, `h(P₋)=P₋` | `h(P₊ x P₋)=P₋ h(x) P₊` |

Both corresponding `(-,+)` identities are also proved for every `x : ClPlus14`.

The key order calculation is

\[
r(P_+xP_-)=r(P_-)r(x)r(P_+)=P_+r(x)P_-.
\]

Reversion exchanges the endpoints and reverses the product; together these preserve the off-diagonal corner. The fixed-observer operation fixes the endpoints, so reversal exchanges the corners. The prose input's claimed reversion corner exchange has the opposite result.

### A nonzero obstruction

Let `τ = sigmaEven 2 = γ₃γ₀` and `w = P₊ τ P₋`. The candidate establishes

\[
w\tau=P_+,\quad P_+\ne0,\quad w\ne0,\quad w^2=0,
\quad r(w)=-w,\quad P_-r(w)P_+=0.
\]

Thus `P₋ r(w) P₊ ≠ r(w)` gives a concrete obstruction to the false opposite-corner assertion. This is an actual nonzero element of the native Clifford algebra.

Only the proof that `P₊ ≠ 0` evaluates an entry under the previously constructed `clPlusToPauli` real algebra homomorphism. The discriminating matrix has real entries. The theorem carrier and witness remain native Clifford expressions; no complex scalar structure or external phase variable is added to them.

The proof order is: Clifford generator relations → complementary projectors → actual involution actions → arbitrary corner laws → transverse nonzero witness → obstruction.

## 3. Source-owner reuse and dependency repair

The new owner imports the existing `HestenesHermitianAdjoint`, which already depends on native `HestenesClPlus14`, native even reversion, and the proven even/Pauli algebra construction. Their established carriers, definitions and theorem statements are reused unchanged.

The Hestenes chain genuinely uses the finite sheet definitions in `TwoSheetThreeColorWeylFinite`. That owner did not use its `ChiralCausalCone` import. Removing only that import disconnects unrelated historical `proofs.*` paths that the maintained scoped Mathlib resolver cannot resolve in this lane. Both direct Hestenes consumers use the finite sheet definitions; the two aggregate consumers already import `ChiralCausalCone` explicitly. The whole owner and these consumers were independently inspected. All theorem bodies in the sheet owner remain unchanged; it also receives the required source header.

No dependency pin, verifier helper, uncertainty owner, umbrella import, or other PR branch is changed. Maintained closure resolution on the actual integrated source succeeds with 11 repository modules and 13 direct Mathlib import roots.

## 4. Intake claims requiring correction or additional constructions

These are source-audit conclusions, not additional Lean declarations in this change.

| Intake claim | Audit disposition |
|---|---|
| Reversion exchanges the two off-diagonal corners | False for these projectors; the native candidate proves preservation and supplies a nonzero obstruction |
| Reversion sends `P₊ A` to `P₋ A` | Sidedness reverses: its image is `A P₋`; `P₊ A` is a principal right ideal |
| A factor `exp(±2γs)` is the observer norm scaling | It scales the quadratic norm value; the corresponding norm scales by `exp(±γs)` |
| A contracting half-line forces irreversible Hardy/Gamow dynamics | The finite exponential evolution remains invertible for both signs of time; a rigged space, domain restriction, or scattering construction is extra data |
| Every isometric rotation is modular flow | A modular identification needs the actual algebra/state or weight and modular/KMS construction |
| Noncollinear loxodromic generators cannot commute | If `[S,B]=0`, then `S+B` and `2S+B` commute and can be linearly independent; a claim about different invariant planes needs precise regularity assumptions |
| Positive uncertainty follows from Krein self-adjointness alone | False: for `K=diag(1,-1)` and `A=[[0,1],[-1,0]]`, the Krein-self-adjoint operator has variance `-1` at the Krein-unit vector `e₁` |
| `J(Rψ)=J(ψ)` | The actual algebraic covariance law is `J(Rψ)=R J(ψ) reverse(R)`; invariance of a Lorentz square does not imply invariance or boundedness of vector components |
| Every nonzero even spinor is invertible and has timelike current | Nonzero singular spinors exist; `P=(1+γ₃γ₀)/2` has `P reverse(P)=0` and null current `(γ₀+γ₃)/2` |
| Positive current proves bounded/stable energy | It does not supply an energy bound or a lower-bounded one-particle Dirac Hamiltonian |
| Current conservation follows from finite Clifford identities alone | It additionally requires an actual differentiable Dirac equation and adjoint identity; slice independence also needs integrability and boundary-flux conditions |
| A universal `2m` bound characterizes stability for all external fields | Potential-step criticality is model-specific; it cannot be promoted to a universal field-stability equivalence |
| The displayed 15-node diagram is a graded poset proving a unique physical synthesis | Its listed covers include rank jumps. A join in a stipulated graph does not establish a unique physical theory |

At the recorded main baseline, the inspected `HestenesDirac.current_conservation` returns a supplied conservation-packet field. It is not a derivation from a PDE. The inspected coordinate `STASpinor.current_j0` is defined as eight squares; connecting it to the native Clifford current requires an actual coordinate/current bridge. The baseline whole-even-algebra Hermitian/matrix-adjoint equivalence is useful infrastructure, but is not itself that current theorem or a Hilbert-space isometry. The newer PR #379 and #380 proposals address further carrier and pairing constructions; their existence is recorded above without claiming their kernel acceptance or a completed Dirac PDE derivation.

For the physical and analytic distinctions, see Hiai, [Concise lectures on selected topics of von Neumann algebras](https://arxiv.org/abs/2004.02383), Sections 2–3; Gavrilov–Gitman, [Quantization of charged fields in the presence of critical potential steps](https://arxiv.org/abs/1506.01156), Sections III and IX; and Dunne, [Heisenberg–Euler effective Lagrangians: Basics and extensions](https://arxiv.org/abs/hep-th/0406216), Section 1.2.2. These references provide context for the audit boundaries; they are not axioms imported by Lean.

## Acceptance scope

The dedicated workflow compiles the complete resolved closure of two native targets: the new spectral-corner owner and the finite sheet owner with its import trim. It audits every declaration owned by both targets, rejects target warnings, and runs source guards on both selected Lean files. The current closure has 11 repository modules. A successful scoped run would not establish a successful complete repository build, native acceptance of the other draft PRs, or the unresolved analytic/physical bridges above.

See [HESTENES_SPECTRAL_CORNERS_REVIEW.md](HESTENES_SPECTRAL_CORNERS_REVIEW.md) for exact hashes, observed results, and pending gates.
