# Hilbert localization and Gram duality: theorem contract

## Provenance and intent

The intake is `Pasted text(20261113-061433).txt`, supplied on 2026-11-13,
SHA-256 `bd31543386a90075f8bea22af36bdc630983313f5148eb6e2de6f2bfdfdb7db0`.
It describes operator localization, compression defects, finite frames, and
porosity in connection with Helge Knutsen,
[arXiv:2204.03068v1](https://arxiv.org/abs/2204.03068v1), *A Fractal
Uncertainty Principle for the Short-Time Fourier Transform and Gabor
Multipliers*.

This contribution constructs the Hilbert-space operator bridge suggested by
the intake. Its carriers are actual, potentially different, complete inner
product spaces over `RCLike` scalars. Neither ambient finite dimension nor
commutation of the bounded endomorphisms is assumed. This is an R4 analytic
contribution under the repository's theorem-contract workflow.

The intake's star-ring formulas do not by themselves construct the Gaussian
STFT, Bargmann transform, Fock space, or Gabor sampling operator in the paper.
In particular, the paper's Lemma 5.2 is a Fock sampling norm formula, not the
intake's generic ring-valued Gram-square identity. The paper's frequency
reflection and lattice normalization would have to be retained in a future
concrete analytic realization.

## Owner discovery and reuse

The inspected upstream base is
`a392af178af1fe2bcba2ba39eb405700c6ee103c`. Owner discovery covered the named
paper terms, alternate projection/corner/Gram formulations, theorem bodies,
native carrier definitions, and related imports and consumers. Absence claims
are restricted to these inspected owners and their relevant Mathlib APIs.

| Existing owner | Reused mathematical surface |
| --- | --- |
| `Core.PeirceCompressionDefect` | Generic noncommutative compression defect and complementary-transfer star-square factorization |
| `Core.PeirceCompressionCStar` | Exact C-star defect norm and equality/commutation criteria |
| `OperatorAlgebra.PartnerEigenspaces` | Actual arbitrary-module `nonzeroEigenspaceEquiv`, with forward map `A` and inverse `mu⁻¹ • B` |
| `OperatorAlgebra.PartnerGeneralizedEigenspaces` | Existing generalized partner eigenspaces; no replacement is introduced |
| `Canonical.PlabicGramEigenvectorTransport` | Existing finite rectangular matrix eigenvector and multiplicity results |
| `Analysis.OperatorDirichletLaplacian` | Existing arbitrary-Hilbert Gram sums, positivity, kernels, and isometry transport |
| `Mathlib.Analysis.InnerProductSpace.Adjoint` | Native adjoints, composition, isometry criterion, range projections, and `norm_adjoint_comp_self` |
| `Mathlib.Analysis.InnerProductSpace.Positive` | Native positive bounded operators and positive adjoint congruence |
| `Mathlib.Analysis.Normed.Operator.NormedSpace` | Norm preservation under postcomposition by a linear isometry |

The separate [draft PR #345](https://github.com/nickgou-nuke/info-geometry-lean/pull/345)
develops same-ring isometry corners, finite operator-valued frames, finite
Weyl masks, empty-hole metric porosity, and conditional multiscale recurrence.
That draft's sources are neither dependencies nor proof authority for this
change; its own validation status must be read separately. This contribution
targets different-carrier bounded operators and their actual ranges.

## Exact claims and dependency order

Let `E` and `F` be complete inner product spaces over `𝕜`, with `[RCLike 𝕜]`.
Write composition in operator order and use the native adjoint `†`.

### 1. Actual range projection and isometric corner transport

For `V : E →ₗᵢ[𝕜] F`, write `v = V.toContinuousLinearMap` and define

\[
P=vv^\dagger,\quad
\operatorname{embed}(T)=vTv^\dagger,\quad
D_S=v^\dagger Sv,\quad T_S=PSP.
\]

Acceptance targets:

- `P` is a native star projection, its range is the actual range of `V`,
  and it equals the native orthogonal projection onto that range.
- Embedding preserves multiplication and adjoints, sends the source identity
  to `P`, and has the exact norm `‖embed T‖ = ‖T‖`.
- `v D_S = T_S v`, `embed D_S = T_S`, and `v† T_S v = D_S`.
- `‖D_S‖ = ‖T_S‖`, including trivial source spaces.
- Forward powers are transported for positive exponents. Pullback powers
  include exponent zero. The ambient embedding is not claimed to send the
  source identity to the ambient identity.

### 2. Projection-symbol localization and exact leakage

For a native star projection `Q : F →L[𝕜] F`, define

\[
D=v^\dagger Qv,\qquad L=(1-P)Qv.
\]

Acceptance targets:

\[
D-D^2=L^\dagger L,\qquad
\operatorname{Re}\langle(D-D^2)x,x\rangle=\|Lx\|^2,\qquad
\|D-D^2\|=\|L\|^2.
\]

The proof must connect the existing noncommutative Peirce defect owner to
these rectangular bounded maps. Positivity is native Hilbert positivity,
not a bare-ring interpretation of a star square. Establish positivity of
`D` and `1-D`, self-adjointness, and contractivity with their actual
analytic hypotheses.

### 3. Quantified loss and conditional contraction

For an isometry `U : E →ₗᵢ[𝕜] F` and star projections `P` on `E` and `Q`
on `F`, the retained and complementary energies satisfy

\[
\|QUPx\|^2+\|(1-Q)UPx\|^2=\|Px\|^2.
\]

An explicit estimate

\[
0\le\delta\le1,\qquad
\delta\|Px\|^2\le\|(1-Q)UPx\|^2\quad(\forall x)
\]

implies `‖QUP‖ ≤ sqrt (1-δ)`. The implication itself only needs `δ ≤ 1`;
positivity of `δ` is used for the strict-contraction conclusion. The exact
energy identity permits any bounded prelocalizer `P`; its projection
hypothesis is used to bound `‖Px‖` by `‖x‖` in the norm estimate.
The case `P=1` also bounds the compressed
positive operator by `‖U† Q U‖ ≤ 1-δ` using its native Gram realization.
This is a conditional theorem: geometric/Gaussian analysis must supply the
quantified lower bound. Conservation alone does not imply strict contraction.

### 4. Actual Hilbert Gram and frame operators

For `A : E →L[𝕜] F`, form `G=A†A` and `S=AA†`. Native composition
associativity already gives the global intertwinings `AG=SA` and
`A†S=GA†`; these are reused identities, not new exported declarations.
Reuse the native adjoint norm theorem and the existing partner eigenspace
owner to establish:

\[
\|G\|=\|A\|^2=\|S\|,
\]

and an actual continuous linear equivalence of the native `mu` eigenspaces when
`mu ≠ 0`, with forward map `A` and inverse `mu⁻¹ • A†`. The nonzero
hypothesis is essential. The underlying linear equivalence is reused from
`PartnerEigenspaces`; continuity is established on the native submodule
topologies. The new application formulas, eigenvalue transport, finite
eigenspace dimension equivalence, and vector inner-product/norm scaling
describe this map directly. No equality of the zero eigenspaces or blanket
equality of spectra on different Hilbert spaces is asserted.

The causal dependencies are isometry/adjoint → actual range projection →
corner transport → defect transport and localization bounds; independently,
partner eigenspaces + adjoint → Hilbert Gram duality. Porosity recurrence
does not follow from these algebraic identities.

## Remaining analytic debt and rejected interpretations

- Construction and isometry of the Gaussian STFT/Bargmann maps on their
  actual weighted function spaces.
- Fock-space subaveraging, infinite lattice sampling, and normalization.
- A geometric lower bound on complementary energy giving an actual
  scale-dependent fractal uncertainty estimate.
- The intake's finite-mask count is not a Euclidean porosity theorem.
- The paper v1 uses measure-zero intersections in its porosity definition;
  geometric thickening arguments require care because null intersection
  need not mean an empty hole. No porosity claim is promoted here.

## Validation and acceptance boundary

The pinned environment is Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; pins remain unchanged.
Candidate authoring, independent semantic review, and independent kernel /
axiom acceptance are separate roles. All Lean compilation uses the shared
build lock. The final validation record will give exact source hashes,
source-closure compilation, every owned declaration's axiom audit, staged
hook and pre-push results, and any dependency obstruction. A narrow source
check will not be reported as a full repository build.
