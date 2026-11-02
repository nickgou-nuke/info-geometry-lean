# Topic note: CAR, Krein symmetry, and projectivization

> **Source review:** 2026-11-02 at [214f7bc](https://github.com/nickgou-nuke/info-geometry-lean/tree/214f7bcf733eaf4720913bc2c082936f2480d3fc). This note reviews the named
> carriers and theorem statements below; it is not a repository-wide proof
> inventory or a report of fresh Lean compilation.

This note separates a finite algebraic model that can be stated precisely from
geometric connections that require additional definitions and proofs. The
repository contains useful pieces of this architecture. Nilpotency, CAR,
a Krein symmetry, and a projective quotient require explicit connecting
maps and metric hypotheses before they can support a single three-mode
projective-metric theorem.

## 1. Nilpotent generators and the doubled space

Let `a₁, …, aₙ` be annihilation operators and `a₁†, …, aₙ†` their adjoints in
an algebra with unit. The canonical anticommutation relations (CAR) are

```text
aᵢ aⱼ + aⱼ aᵢ       = 0
aᵢ† aⱼ† + aⱼ† aᵢ†   = 0
aᵢ aⱼ† + aⱼ† aᵢ     = δᵢⱼ 1.
```

In particular, each generator is nilpotent. Nilpotency and mutual
anticommutation among the `aᵢ` alone do **not** imply the mixed CAR relation;
the adjoint generators and their normalization are additional structure.

On the real span of the `2n` CAR generators, set

```text
γᵢ⁺ = aᵢ + aᵢ†,       γᵢ⁻ = aᵢ − aᵢ†.
```

Then `(γᵢ⁺)² = 1`, `(γᵢ⁻)² = −1`, and distinct generators anticommute.
With this normalization they give a representation of the real Clifford
relations of signature `(n,n)`. Equivalently, a paired basis has the split
quadratic form `η = diag(Iₙ, −Iₙ)`. In the isotropic basis, the same form has
matrix

```text
η = [0  Iₙ]
    [Iₙ  0 ].
```

These matrices describe the same form in different bases.

## 2. Null subspaces, operators, and zero modes

For the off-diagonal form above, the two coordinate summands are totally
isotropic. If `I₊` is one such subspace, useful operator classes are

```text
Nₗ = {A : A|I₊ = 0}
Nᵣ = {B : im B ⊆ I₊}.
```

For `ψ ∈ I₊`, `A ∈ Nₗ`, and `B ∈ Nᵣ`, one has `Aψ = 0` and
`⟨ψ, Bψ⟩η = 0`, respectively. The second equality uses that `I₊` is totally
isotropic. These elementary facts do not, by themselves, identify either
class with a GNS kernel or establish an operator-algebraic quotient.

Fermion parity acts by a sign on odd CAR generators: if `P = (−1)^F`, then
`PγP = −γ` (equivalently, `Pγ = −γP`). Thus an odd Majorana generator
**anticommutes** with parity; it does not commute with it. Calling a Majorana a
zero mode also requires a specified Hamiltonian or Dirac operator and a
proved kernel or commutator statement on a specified representation. The
algebraic CAR relations alone do not establish topological protection.

## 3. Fundamental symmetry

A fundamental symmetry on a Hilbert space is represented here by a bounded
operator `J` satisfying `J² = 1` and `J* = J`. For the off-diagonal split
form, the sheet swap

```text
J = [0  Iₙ]
    [Iₙ  0 ]
```

satisfies `J² = 1`; moreover `ηJ = I`. It therefore converts the indefinite
form into the positive form `⟨x,y⟩J = η(x,Jy)` in this model. For a general
Krein space, positivity and compatibility with the chosen indefinite form
must be part of the hypotheses; the two operator equations alone are not a
complete definition in arbitrary coordinates.

## 4. Scale quotient and volume data

The quotient

```text
(V \\ {0}) / ℝ>0
```

identifies vectors that differ by a positive scalar. It is a space of
oriented rays: `x` and `−x` remain distinct. The usual real projective space
also identifies negative rescalings, using `ℝˣ` (or `ℝ \\ {0}`). These are
different quotients and should not be described interchangeably.

A positive homothety `x ↦ λx` rescales a quadratic form by `λ²`. Berezinians
and Pfaffians can encode volume information in their appropriate settings,
but they are not a universal extra quotient on an arbitrary real vector
space. A Berezinian requires an invertible map of a specified graded space;
a Pfaffian applies to a specified skew-symmetric form or matrix of even rank.
The identity `Pf(Ω)² = det(Ω)` belongs to that setting, with conventions
stated for the chosen basis and normalization.

## 5. Linear deformations and metrics

For `J = diag(Iₙ, −Iₙ)`, every real endomorphism has block form

```text
X = [A  B]
    [C  D].
```

Conjugation by `J` separates block-diagonal and off-diagonal parts:

```text
X₊ = (X + JXJ)/2 = [A  0]
                         [0  D]
X₋ = (X − JXJ)/2 = [0  B]
                         [C  0].
```

This is a genuine two-part decomposition of `gl(2n,ℝ)`. It does not give the
claimed three-mode decomposition into scale, chiral, and volume terms. In
particular, `gl(2n,ℝ)` has dimension `4n²`; a scalar, one constrained
off-diagonal block, and a diagonal block of the form
`diag(A,−Aᵀ)` with `tr A = 0` cannot span it. Any finer decomposition needs
its subspaces, dimensions, metric, and orthogonality proved explicitly.

The repository now also formalizes a finite 2×2 matrix analogue in
[lean/InfoGeometry/Projective/ProjectiveKreinDecomposition.lean](lean/InfoGeometry/Projective/ProjectiveKreinDecomposition.lean): every real
2×2 matrix is a sum of a scalar-diagonal part, an off-diagonal part, and a
traceless-diagonal part, and these parts are pairwise orthogonal for the
Frobenius inner product `Tr(AᵀB)`. This is a concrete low-dimensional linear
algebra result. It is not the proposed general `gl(2N,ℝ)` decomposition, and
its Frobenius squared norm is not the claimed projective distance.

Likewise, the expression

```text
arcosh(|⟨u,v⟩η| / sqrt(⟨u,u⟩η ⟨v,v⟩η))
```

is not a distance on the full positive-norm cone of signature `(n,n)` when
`n ≥ 2`: two orthogonal positive-norm vectors make the argument zero. A
Cayley–Klein or hyperbolic distance requires a more specific domain, such as a
same-time-orientation timelike cone in Lorentzian signature, and its metric
normalization must be stated. A scale/chiral/volume Pythagorean identity
further requires an actual metric and an orthogonal tangent-space splitting;
it does not follow from a quotient or block decomposition alone.

## 6. What the cited Lean modules establish

The cited source modules supply formal statements with the following
carriers and hypotheses:

| Area | Lean owner | Formalized scope |
|---|---|---|
| Nilpotency versus CAR | [lean/InfoGeometry/Canonical/LightConeCARFockBridge.lean](lean/InfoGeometry/Canonical/LightConeCARFockBridge.lean) | Explicitly distinguishes a nilpotent light-cone pair from a CAR pair and requires a CAR realization. |
| Split `Cl(1,1)` example | [lean/InfoGeometry/Krein/DoubledKreinMobiusTwist.lean](lean/InfoGeometry/Krein/DoubledKreinMobiusTwist.lean) | Proves nilpotency and a mixed CAR relation for concrete split-Clifford generators. |
| Fundamental symmetry | [lean/InfoGeometry/Krein/DoubledKreinMobiusTwist.lean](lean/InfoGeometry/Krein/DoubledKreinMobiusTwist.lean) | Defines an involutive self-adjoint symmetry and the induced Krein adjoint. |
| Common and relative sheet scales | [lean/InfoGeometry/Canonical/RestrictedVolumeCharacter.lean](lean/InfoGeometry/Canonical/RestrictedVolumeCharacter.lean) | Splits two scalar sheet parameters into common and relative parts. |
| Finite projective quotient | [proofs/ProjectiveSheetV4.lean](proofs/ProjectiveSheetV4.lean) | Quotients a finite Pin extension by a central sign; it is not the positive-ray quotient of a real vector space. |
| Pfaffian layer | [lean/InfoGeometry/Volume/Pfaffian.lean](lean/InfoGeometry/Volume/Pfaffian.lean) | Uses a square-root-of-absolute-determinant definition and states a 2D identity; it is not a general Pfaffian construction. |
| Horizontal/vertical split | [lean/InfoGeometry/Epistemology/RiemannianSubmersion.lean](lean/InfoGeometry/Epistemology/RiemannianSubmersion.lean) and [lean/InfoGeometry/Canonical/NaturalGradientSubmersionFlow.lean](lean/InfoGeometry/Canonical/NaturalGradientSubmersionFlow.lean) | Gives projector and metric-collapse lemmas; it does not establish the proposed projective three-mode metric. |
| 2×2 matrix analogue | [lean/InfoGeometry/Projective/ProjectiveKreinDecomposition.lean](lean/InfoGeometry/Projective/ProjectiveKreinDecomposition.lean) | Proves scalar ratio homogeneity, a 2×2 matrix reconstruction, pairwise Frobenius orthogonality, and the resulting Pythagorean identity. It does not prove the general Krein/projective metric claim. |

### Conditional tripotent parity and kernel results

The reviewed revision also contains the following results. They concern
specified real-algebra or endomorphism carriers; they do not identify an odd
CAR Majorana generator with an operator commuting with fermion parity.

| Owner and result | Hypotheses and established conclusion | Boundary |
|---|---|---|
| [PeirceSpine/TripotentParity.lean](lean/InfoGeometry/OperatorAlgebra/PeirceSpine/TripotentParity.lean): `oddGrade_projZero`, `evenGrade_projZero`, `parityConj_projZero_of_mem_fiveGradeRange` | In `[Ring A] [Algebra ℝ A]`, the odd part for `P₀ = 1 - T*T` is the sum of adjoint grades `−1,+1`; the even part is the sum of grades `−2,0,+2`. The polynomial regroupings need no tripotence. With `T*T*T = T`, conjugation by `invS P₀` acts on each grade range with the corresponding sign. | The zero-mode cut differs from the positive/negative spectral cut. `T*T` remains an operator. |
| [Core/TripotentChiralRestriction.lean](lean/InfoGeometry/Core/TripotentChiralRestriction.lean): `anticommute_endProjZero`, `zeroModeRestriction_sq_of_anticommute`, `zeroModeChiralEquiv` | For `T Γ : Module.End ℝ V`, anticommutation `Γ*T = -(T*Γ)` implies commutation with `1 - T*T` and exchange of the positive/negative polynomial projectors. With `T^3 = T` and `Γ*Γ = 1`, the restriction of `Γ` to `zeroModeCarrier T = ker T` is an involution and a real linear equivalence. | The result preserves the existing kernel; it does not produce a nonzero kernel vector, identify `Γ` with a CAR Majorana, or prove topological protection. |
| [Physics/NuclearFiveGradeParity.lean](lean/InfoGeometry/Physics/NuclearFiveGradeParity.lean): `totalParity_invariant_of_fiveGrade`, `totalParity_invariant_projected_block` | For a tripotent `T` in an associative real algebra, diagonal coefficients in grade `0` and transition coefficients in grades `+1,−1` make the block Hamiltonian invariant under the combined internal/external parity. Applying the five-grade projectors constructs such a block from arbitrary four inputs. | The theorem is a parity-invariance statement for this block Hamiltonian. It does not assert that an individual odd CAR generator commutes with fermion parity. |

The kernel involution and the zero-mode Peirce parity are distinct actions.
Their relation to a Hamiltonian, CAR representation, or projective metric
must be stated through a map and theorem on the chosen carrier. These
conditional positive results preserve the qualifications in Sections 2–5.

## 7. Existing Madelung and chiral-fluid lanes

The following Madelung and chiral-fluid owners provide separately stated
results. Their names and shared vocabulary do not make them one derived
quantum-fluid theorem.

| Lane | Lean owner(s) | What the source proves, and its boundary |
|---|---|---|
| Differential Madelung calculus | [lean/InfoGeometry/Algebra/MadelungDerivation.lean](lean/InfoGeometry/Algebra/MadelungDerivation.lean), [lean/InfoGeometry/Algebra/MadelungLogDensityCalculus.lean](lean/InfoGeometry/Algebra/MadelungLogDensityCalculus.lean) | Derivation-algebra identities for amplitude curvature, logarithmic density score, Hamilton–Jacobi residual to Euler residual, quantum Euler, and amplitude transport to continuity. The continuity theorem assumes the transport equation; it does not derive it from Schrödinger evolution. |
| Fisher–Rao/amplitude relation | [lean/InfoGeometry/Information/FisherRaoMadelungIsometry.lean](lean/InfoGeometry/Information/FisherRaoMadelungIsometry.lean), [lean/InfoGeometry/Canonical/MadelungFisherRaoSynthesisBridge.lean](lean/InfoGeometry/Canonical/MadelungFisherRaoSynthesisBridge.lean) | Square-root density identities and the scalar line-element identity under `dρ = 2u du`; the synthesis bridge assumes the amplitude/density and quantum-potential equations in its hypotheses. It does not construct a full infinite-dimensional Riemannian isometry. |
| Discrete Madelung state | [lean/InfoGeometry/Canonical/MadelungHydrodynamicPressureBridge.lean](lean/InfoGeometry/Canonical/MadelungHydrodynamicPressureBridge.lean), [lean/InfoGeometry/Canonical/MadelungHydrodynamic.lean](lean/InfoGeometry/Canonical/MadelungHydrodynamic.lean) | A finite lattice state with positive density and phase gradient, velocity proportional to that gradient, and a quantum-potential expression using a supplied Laplacian of `√ρ`. The synthesis theorem reduces to the velocity identity and the zero-Laplacian special case; no discrete evolution or continuity law is defined there. |
| Spinor density and current | [lean/InfoGeometry/Canonical/SpinorHydrodynamicReadout.lean](lean/InfoGeometry/Canonical/SpinorHydrodynamicReadout.lean) and its consumers `SpinorReadoutRegularity.lean`, `SpinorReadoutOscillation.lean` | Defines density as norm square, current as the imaginary part of a complex inner product, and current/density readout away from zero density; proves bounds and derivative formulas. It explicitly does not posit wave evolution or derive a continuity equation. |
| Doubled amplitude and Krein sheets | [lean/InfoGeometry/Canonical/PolarizedMadelungBridge.lean](lean/InfoGeometry/Canonical/PolarizedMadelungBridge.lean), [lean/InfoGeometry/Canonical/MadelungMoebiusChiralBridge.lean](lean/InfoGeometry/Canonical/MadelungMoebiusChiralBridge.lean), [lean/InfoGeometry/Krein/FiniteMadelungPhaseRotation.lean](lean/InfoGeometry/Krein/FiniteMadelungPhaseRotation.lean) | Uses the existing doubled real carrier, Hilbert normalization, positive/negative sheet projections, sheet densities, phase orbit, and finite real phase rotations. The Möbius/chiral bridge transports the sheet decomposition to existing idempotents; this is not a fluid-current evolution theorem. |
| Chiral BdG and Krein compatibility | [lean/InfoGeometry/Physics/BdGChiralBlockMatrix.lean](lean/InfoGeometry/Physics/BdGChiralBlockMatrix.lean), [lean/InfoGeometry/EmergentVacuum/SplitChiralBdGCompatibility.lean](lean/InfoGeometry/EmergentVacuum/SplitChiralBdGCompatibility.lean) | Finite matrix identities for chiral grading, off-diagonal Dirac/BdG blocks, and a split-Krein/Peirce compatibility model. These modules do not identify their matrix state with the discrete Madelung state or the spinor current above. |
| Vorticity/chirality and Navier–Stokes-labelled results | [lean/InfoGeometry/Canonical/MadelungTopologicalSpin.lean](lean/InfoGeometry/Canonical/MadelungTopologicalSpin.lean), [lean/InfoGeometry/Canonical/MadelungNavierStokesClosure.lean](lean/InfoGeometry/Canonical/MadelungNavierStokesClosure.lean), [lean/InfoGeometry/Physics/ArnoldHydrodynamicsBeltrami.lean](lean/InfoGeometry/Physics/ArnoldHydrodynamicsBeltrami.lean), [lean/InfoGeometry/Physics/SDiffCoadjointHelicityCasimir.lean](lean/InfoGeometry/Physics/SDiffCoadjointHelicityCasimir.lean) | The spin/vorticity equivalence assumes the operator identity `V = c • ChiralityOp`. The closure theorem assumes a skew-adjoint velocity field and applies the existing residual lemma; the Beltrami and helicity results are algebraic or conditional identities. These assumptions do not establish a PDE solution, fluid existence theorem, or derivation of vorticity from the Madelung current. |
| Finite-to-colimit observable lane | [lean/InfoGeometry/Canonical/MadelungMetriplecticTomitaFrame.lean](lean/InfoGeometry/Canonical/MadelungMetriplecticTomitaFrame.lean), [lean/InfoGeometry/Canonical/MadelungMetriplecticColimitBridge.lean](lean/InfoGeometry/Canonical/MadelungMetriplecticColimitBridge.lean), consumed by [lean/InfoGeometry/TraceFormula/OperatorialISColimitFramework.lean](lean/InfoGeometry/TraceFormula/OperatorialISColimitFramework.lean) | Packages finite trace/action data and transports an observable action into the algebraic UHF colimit. It does not transport a continuity equation, chiral current, or Navier–Stokes evolution through that colimit. |

Several local identities and conditional bridges already exist. To join
the models in this note, a connecting construction must provide explicit
carrier maps and evolution theorems. A useful dependency order is:

1. Choose one finite graph or lattice carrier and define a complex state,
   self-adjoint Hamiltonian, density, and edge current on that same carrier.
2. Prove norm conservation and a local continuity equation from the stated
   discrete Schrödinger evolution. Then express the state in amplitude/phase
   form and reuse the existing Fisher–Rao and Madelung identities where their
   hypotheses match.
3. Define the chiral/BdG grading on that carrier and prove how it acts on the
   Hamiltonian and current. Separately prove the compatibility map to the
   doubled Krein sheets; do not identify the grading with the fundamental
   symmetry without a theorem.
4. Specify the quotient actually used (positive rays, real projective classes,
   or phase orbits), construct the descended observables, and prove the
   quotient map respects the finite evolution. Do not infer a projective
   distance or three-mode tangent metric from scalar scale invariance.
5. Only after the finite evolution square commutes, prove its compatibility
   with the existing algebraic colimit maps. Keep Beltrami/helicity and
   Navier–Stokes PDE claims conditional until their analytic carrier and
   hypotheses are present.

This gives a dependency graph with parallel prerequisites rather than one
unjustified chain:

```mermaid
flowchart LR
  A[Complex state and finite Hamiltonian] --> B[Discrete Schrödinger evolution]
  B --> C[Norm conservation and edge-current continuity]
  C --> D[Amplitude/phase Madelung identities]
  D --> E[Density and Fisher–Rao readout]
  A --> F[Chiral/BdG grading]
  F --> G[Proved map to doubled Krein sheets]
  E --> H[Chosen projective or phase quotient]
  G --> H
  C --> I[Finite observable/evolution map]
  I --> J[Colimit compatibility]
  H --> I
```

### Dependency map

The concepts form a dependency partial order, not one theorem chain. The
arrows below mean that a later construction needs the earlier structure; they
do not claim that the earlier data imply the later relations.

```mermaid
flowchart LR
  A1[Nilpotent generators] -->|add mixed CAR normalization| A2[CAR relations]
  A2 --> A3[Majorana combinations]
  A4[Split Krein form] --> A5[Fundamental symmetry J]
  A4 --> A6[Isotropic subspaces]
  A6 --> A6b[One-sided operator classes]
  A7[Vector space] --> A7b[Positive-ray or real-projective quotient]
  A8[Finite block-matrix carrier] --> A8b[Orthogonal matrix decomposition]
  A9[Metric and orthogonal tangent splitting] --> A9b[Pythagorean identity]
  A7b --> A9
```

The projective quotient needs a vector space and a chosen equivalence
relation; it does not require `J`. Conversely, a quotient carrying a metric
needs additional metric data. The two off-diagonal CAR generators, a split
Krein carrier, and a projective state space remain separate models until a
specific map between them is defined and proved. The proposed dimensions for
a general four-way `gl(2N,ℝ)` split are only a numerical identity unless
actual subspaces, a direct-sum theorem, and the relevant projections are
provided.

Accordingly, a link in the proposed chain needs an explicit map and theorem
connecting its carriers. The conditional parity and kernel results in
Section 6 establish a symmetry of a specified block Hamiltonian and an
involution on the kernel of a specified tripotent; neither changes the odd
CAR anticommutation law or supplies a nonzero, topologically protected
Majorana mode. The volume constructions and quotient data cited here also
do not by themselves yield a Berezinian/Pfaffian projectivization or a
general three-mode metric. The 2×2 result remains a statement about its
explicit matrix carrier and Frobenius product.
