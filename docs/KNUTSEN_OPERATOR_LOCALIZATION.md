# Operator localization, frames, and geometric depletion

## Provenance and scope

This work formalizes the valid operator and scalar content of the supplied
`Pasted text(20261112-215043).txt`, using existing repository owners and native
Mathlib objects. The literature reference is Helge Knutsen,
*A Fractal Uncertainty Principle for the Short-Time Fourier Transform and Gabor
Multipliers*, [arXiv:2204.03068v1](https://arxiv.org/abs/2204.03068v1).
The [accessible v1 manuscript](https://www.researchgate.net/publication/359813942_A_Fractal_Uncertainty_Principle_for_the_Short-Time_Fourier_Transform_and_Gabor_multipliers)
identifies that version in its header. Equation numbering here refers to v1.

Intake SHA-256:
`bd31543386a90075f8bea22af36bdc630983313f5148eb6e2de6f2bfdfdb7db0`.

The results concern bounded Hilbert-space operators, finite Hilbert-space
frames, finite families over noncommutative star rings, two-by-two matrix
conjugation, and a real scalar recurrence. They do not construct the Gaussian
STFT, Bargmann transform, Bargmann--Fock function space, porous subsets,
Gabor lattices, or a fractal uncertainty principle.

The initiating algebraic identities alone cannot imply norm decay: taking
the isometry, symbol, and projections to be the identity satisfies those
identities while leaving localization norm equal to one on a nonzero Hilbert
space. An analytic hypothesis must connect the operators to the scalar estimates.

## Native Hilbert-space contract

Owner: `InfoGeometry.OperatorAlgebra.IsometricCompression`.

Let `𝕜` be RCLike, let `E` and `F` be complete inner-product spaces over `𝕜`,
and let `V : E →ₗᵢ[𝕜] F`. Write `v` for its continuous linear map. The actual
constructed operators are

\[
P=vv^*,\qquad C(S)=v^*Sv,\qquad J(T)=vTv^*,
\qquad L(S)=(I-P)Sv.
\]

There is no finite-dimensional, nonzero-space, or surjectivity assumption.
The file proves that `P` is an `IsStarProjection` and that its native linear
range equals the range of `v`. It proves

\[
C(J(T))=T,\qquad J(C(S))=PSP,\qquad
\|J(T)\|=\|T\|,\qquad \|C(S)\|=\|PSP\|.
\]

Supported extension preserves ordered multiplication and adjoints. Compression
preserves adjoints and satisfies `C(1 - S) = 1 - C(S)`. It is not claimed to
preserve arbitrary products.

For an ambient orthogonal projection `Q`, the formal results include

\[
C(Q)=(Qv)^*(Qv),\qquad
\|C(Q)\|=\|Qv\|^2\le1,
\]

\[
(Qv)^*(Qv)+((I-Q)v)^*((I-Q)v)=I,
\]

\[
C(Q)-C(Q)^2=L(Q)^*L(Q),\qquad
\|C(Q)-C(Q)^2\|=\|L(Q)\|^2.
\]

Both the compression and its idempotency defect are positive in Mathlib's
native `ContinuousLinearMap.IsPositive` sense. Finally,

\[
C(Q)\text{ is an orthogonal projection}
\iff L(Q)=0
\iff Q(\operatorname{range}v)\subseteq\operatorname{range}v.
\]

The final condition uses `Module.End.invtSubmodule`, not a field assuming
the desired conclusion. This corrects the intake's implicit inference that
compressing a projection by an arbitrary one-sided isometry preserves idempotency.

### Existing owners

The ambient Gram factorization comes from
`Core.PeirceCompressionDefect.compression_adjoint_mul_defect`; the new file
transports it between the two Hilbert spaces. The existing
`Core.PeirceCompressionCStar` already owns ambient defect-norm and zero-transfer
criteria. `Projective.ProjectionCovariance` covers the separate case of a
surjective `LinearIsometryEquiv`.

Open PR #326 was inspected. Its `UnitaryCornerCompression` concerns conjugation
by a unitary inside one star ring. The distinct-space embedding and range-corner
norm equality here do not replace that work.

## Finite Hilbert-space frames

Owner: `InfoGeometry.OperatorAlgebra.FiniteFrameMultipliers`.

For a finite index type and actual vectors `φ : ι → E`, `synthesis φ` is a
bounded map from `EuclideanSpace 𝕜 ι` to `E`. The file proves

\[
Bc=\sum_i c_i\varphi_i,\qquad
(B^*x)_i=\langle\varphi_i,x\rangle,\qquad
BB^*=\sum_i |\varphi_i\rangle\langle\varphi_i|.
\]

It uses Mathlib's `Matrix.gram` and `InnerProductSpace.rankOne`. The Gram-square
identity inserts `BB*` between the two vectors. Under the explicit Parseval
assumption `BB* = I`, the Gram matrix is idempotent, the Gram operator `B*B` is
an orthogonal projection, and `analysisIsometry` constructs the native isometry
`B*`. A finite redundant family is allowed.

Scalar-weighted multipliers satisfy adjoint and complementary-mask identities,
and nonnegative real weights give positive operators. The factorization
`M_b = B D_b B*` uses the actual coefficient operator `D_b`. For a Parseval
family, `multiplier_eq_compress` identifies it with the preceding isometric
compression. An indicator on a finite set of coefficient indices produces an
orthogonal projection on coefficient space. No metric porosity follows from
selecting those indices.

## Finite operator families

Owner: `InfoGeometry.OperatorAlgebra.FiniteOperatorFamilies`.

The intake also uses `φ : ι → A` and operator-valued weights `b : ι → A` in an
arbitrary star ring. These form a separate algebraic model and are not
identified with the Hilbert-space vectors above. Multiplication order is
retained in `∑ i, φ i * b i * star (φ i)`. The Gram expression uses the native
outer-product matrix `Matrix.vecMulVec (star φ) φ`, and its projection statement
assumes the actual identity `dotProduct φ (star φ) = 1`. No norm or ordered
positivity is inferred in this general ring setting.

## Geometric depletion over the real numbers

Owner: `InfoGeometry.Analysis.GeometricPorosity`.

The real-valued sequence is

\[
s_0=\nu,\qquad s_{n+1}=s_n-(\nu/3)^{n+1}.
\]

For every real `ν`, the file proves its finite-sum expression and

\[
(3-\nu)s_n=\nu(2-\nu)+\nu(\nu/3)^n.
\]

For `0 ≤ ν ≤ 1`, it proves antitonicity, `ν/2 ≤ s_n ≤ ν`, the natural-power
bound `1 - s_n^m ≤ 1 - (ν/2)^m`, and actual real convergence to
`ν(2 - ν)/(3 - ν)`.

The conditional iteration theorem explicitly assumes a nonnegative sequence
and the one-step bound

\[
a_{n+1}\le(1-s_n^{2d})a_n.
\]

It then proves `a_n ≤ q^n a_0` for `q = 1 - (ν/2)^(2*d)`, and convergence to
zero when `0 < ν ≤ 1`. Natural `d = 0` is valid: the supplied hypothesis forces
subsequent terms to vanish. The endpoint `ν = 0` is supported by the scalar
bounds, not by the positive-parameter decay conclusion.

In v1, equation (3.9) expresses the constants through a ratio of geometric
radii. This recurrence is its geometric-sum specialization. The paper's
operator iteration also has a scale-dependent analytic factor; that factor
and the one-step operator estimate are not supplied by this scalar file.

## Four-term matrix averaging

Owner: `InfoGeometry.OperatorAlgebra.PauliAveraging`.

The construction reuses `Gamma_mat`, `J_mat`, and `K_mat` from
`Clifford.OperatorValuedJones`, in namespace `InfoGeometry.Clifford`.
For every matrix over an arbitrary star ring, it proves

\[
M+\Gamma M\Gamma^*+J M J^*+K M K^*
=\operatorname{diag}(2(M_{00}+M_{11}),2(M_{00}+M_{11})).
\]

The sum composed with itself is four times the sum. The four conjugates of
the first coordinate projection sum to twice the unit, while that projection
and its exchange conjugate sum to the unit. These identities remain valid in
characteristic two; distinctness of the four matrices is not asserted.

The equal diagonal coefficient is not claimed to be central. This is not a
cyclic trace construction on a noncommutative coefficient ring. A nonzero
orthogonal projection has operator norm one, so the single-coordinate example
supplies no strict contraction.

## Corrected attribution and dependency order

The manuscript's Lemma 5.2 is a weighted Fock-space sampling expression for a
Gaussian Gabor multiplier norm; it is not the finite Gram-square identity.
Its Bargmann correspondence also reflects the symbol, `Sᶜ(z) = S(conj z)`.
Those analytic identifications are outside these files.

The established dependencies are:

1. The existing Peirce Gram identity and native adjoints support
   `IsometricCompression`.
2. Native rank-one synthesis constructs Parseval analysis; the proved
   `multiplier_eq_compress` bridge connects it to `IsometricCompression`.
3. Native outer-product identities support the separate operator-family
   algebra. Existing sheet matrices support the four-term finite average.
4. The real geometric recurrence supports its explicitly conditional scalar
   iteration theorem.

There is no proved edge from the recurrence to a localization-operator bound,
or from finite averaging to porous-set geometry. Actual STFT/Bargmann
constructions, subaveraging/Nyquist-density estimates, geometric thickening,
lattice-cell hypotheses, and a bound `C * h^β` remain open work.

## Validation and reproduction

The validation environment uses Lean `4.34.1`, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, on base commit
`a392af178af1fe2bcba2ba39eb405700c6ee103c`.

With that compiler on `PATH`, the maintained source-closure checker supports
these owners explicitly:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root .lake/packages/mathlib \
  --lean lean \
  --target InfoGeometry.OperatorAlgebra.IsometricCompression \
  --target InfoGeometry.OperatorAlgebra.FiniteFrameMultipliers \
  --target InfoGeometry.OperatorAlgebra.FiniteOperatorFamilies \
  --target InfoGeometry.OperatorAlgebra.PauliAveraging \
  --target InfoGeometry.Analysis.GeometricPorosity \
  --output /tmp/knutsen-native-review
```

Use a fresh output directory for an acceptance run, without `--incremental`
or `--skip-audit`. The checker compiles the transitive repository imports,
records source and artifact hashes, and inspects the axiom dependencies of
every owned declaration in the five selected modules. New-owner warnings
must be checked explicitly because this checker's built-in warning-failure
prefix is specific to its original Clifford--Dirac targets.

The source-closure result, static source scans, independent semantic review,
independent QA, root file checks, targeted Lake build, and actual pre-push
hook result are separate evidence. The publication receipt records their
observed outcomes; none is a whole-repository certificate. The root Lake
configuration also requires local `HomotopyHypothesis` and `Atlas` packages
whose full checkout revisions are not supplied at this base. Reproducing
that workspace requires the canonical external checkouts, without substituting
guessed revisions or changing the tracked dependency pins.
