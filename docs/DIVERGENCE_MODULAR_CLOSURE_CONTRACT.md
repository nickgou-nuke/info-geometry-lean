# Distribution, Gaussian, and relative-modular divergence connections

## Intake and purpose

The user asked to recover the existing divergence calculus, exponential-family
dual geometry, Gaussian scale and shape, common/chiral trace decomposition,
Jaynes reference states, and determinant/Pfaffian/Berezinian Jacobian
factorizations. After a source audit, the user instructed:

> lets do it and close the theoretical framework

This change implements the concrete missing connections identified by that
audit. It uses the source tree published in PR #410, commit
`abc8365b24c3ba6292fba3a83a8d36a99903bd84`, as its mathematical base.

The acceptance target is a connected finite-dimensional theorem chain with
explicit carriers, normalization, inverse, positivity, and differentiation
hypotheses. A statement about this chain does not certify infinite-dimensional
Type III standard form, a supermanifold, or a physical spacetime model.

## Intended theorem contracts

### Positive distributions and their actual derivatives

Reuse `PositiveMeasure.gklTerm`, `generalizedKL`, the projective/radial split,
the scalar Itakura--Saito owner, and the finite exponential-family owners.
For positive values and actual derivatives of the two input paths, prove the
first variation of the existing generalized-KL sum. On affine lines prove its
actual second directional derivative, including the relative Fisher form at
coincident distributions. Preserve the weight and reversed ratio in
`gklTerm p q = p * IS(q / p)`.

Connect the existing log-sum-exp derivative theorem to the finite family's
mean statistic, then remove the supplied derivative/mean premise from the
KL--Bregman corollary. The reference probability remains explicit.

### Actual Gaussian measures and covariance divergence

For arbitrary real strictly positive-definite covariance matrices, evaluate
Mathlib's `InformationTheory.klDiv` on actual
centered `ProbabilityTheory.multivariateGaussian` measures. Use invertible pushforward
invariance, covariance whitening, and product Gaussian integration. Neither a
commuting-pair premise nor a scalar replacement for the full covariance is
allowed.

Connect this measure theorem to the existing `Jordan.steinLoss`. Construct the
isotropic relative scale and determinant-one relative shape, and prove

`steinLoss X Y = n * burgKernel s + s * (trace S - n)`.

Here `s > 0` and `det S = 1` are proved properties of the actual relative
distortion, not fields supplied to a wrapper. The scale factor on the shape
term is retained. A full-matrix nonnegativity result must consume a proved
Gaussian KL or spectral inequality.

### Actual relative modular operator and its logarithm

Construct the full finite relative modular operator with action
`Delta(X) = sigma * X * rho^{-1}` on a Hilbert--Schmidt carrier. Prove its
positive spectral realization and its actual functional-calculus logarithm.
For the vector `sqrt rho`, prove the normalized expectation and logarithm
identities that identify the existing IS defect with actual matrix relative
entropy. Noncommuting source/reference matrices remain in scope.

Specialize this concrete expectation to the existing generalized Gibbs
charge/entropy balance, preserving its real parameter vector and potentially
noncommuting Hermitian charges.

The abstract `RelativeModularDatum.relativeLogBetween` and the algebraic
normalization-cancellation theorem are context; supplying their desired
conclusions as new fields is not an implementation of this contract.

## Reused owners and scope distinctions

- `PositiveMeasure`, `Projective.GaugeReduction`: finite positive weights and
  their native normalization, generalized KL, and exact mass split.
- `Analytic.LogSumExp`, `ExponentialFamily.KLBregman`: actual finite partition
  derivatives and the existing KL/Bregman interface.
- `Jordan.SPD`, `Jordan.BurgStein`: real SPD matrices and full trace/logdet loss.
- `Canonical.MatrixRelativeEntropy`: concrete CFC logarithms and full-matrix
  Klein inequality from PR #410.
- `Physics.FiniteRelativeModularOperator`: actual left/right multiplication.
- `Quantum.OperatorTraceShapeDecomposition`: algebraic paired trace and
  supertrace projections, not an automatically positive logarithm.
- `NCG.BerezinianGaussianFactorization`: ordered Schur factorization; ordinary
  commutative determinant readouts do not provide general supercommutative
  Berezinian multiplicativity.

The earlier audit distinguishes finite probability mass scale, covariance
scale, and the common/relative scale of graded sectors. These quantities are
not identified merely because each admits logarithmic coordinates.

## Validation and provenance

The Lean and Mathlib pins are unchanged. Candidate authoring, independent
semantic review, and independent acceptance use distinct agent contexts.
Builds are serialized through the repository's shared lock. Final evidence
must include fresh compilation of the selected source closure, every owned
declaration's transitive axiom audit, source and helper hashes, and strict
source-quality checks.

The Gaussian KL/product proof is adapted from
[`StatLean/Stat-Lean`](https://github.com/StatLean/Stat-Lean/tree/e436d8a184421c2a0ed8db0b2688c6cd26a7f5a2),
commit `e436d8a184421c2a0ed8db0b2688c6cd26a7f5a2`, specifically
`StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean` and `KLDivergence.lean`.
That source uses the same Lean and Mathlib pins. The adapted files preserve
the Apache 2.0 attribution to Junwei Lu and StatLean contributors, identify
the source revision, and describe the modifications. They introduce no new
package dependency. The diagonal-product proof has been replaced by a direct
real square-root and affine-pushforward argument. The relative trace/logdet
nonnegativity is exposed independently before taking the KL value's `toReal`.

The root package has a previously observed missing
`external_refs/homotopy-hypothesis-lean4` path dependency. This is an integration
condition to recheck and disclose, separately from native scoped compilation.
No whole-repository build result is inferred from a focused check.

## Canonical mathematical chain

### 1. Positive distributions and their local metric

For finite positive weights, the existing divergence is

\[
G(p,q)=\sum_i\left[p_i\log(p_i/q_i)-p_i+q_i\right].
\]

The new first-variation theorem differentiates the actual functional along
two independently moving paths:

\[
\frac{dG}{dt}
=\sum_i\left[\dot p_i\log(p_i/q_i)
  +\dot q_i(1-p_i/q_i)\right].
\]

On affine paths through positive `p,q`, its actual second derivative is

\[
\left.\frac{d^2}{dt^2}G(p+tu,q+tv)\right|_{t=0}
=\sum_i\frac{(u_i-(p_i/q_i)v_i)^2}{p_i}\ge0.
\]

At `p=q` this is the Fisher quadratic form of the relative tangent `u-v`.
These theorems concern the finite positive cone. For the probability-simplex
interpretation, also impose mass one and zero-sum probability tangents.
Analytic variation of a distribution functional is distinct from an algebra
derivation satisfying the noncommutative Leibniz rule.

Writing `IS(x,y)=x/y-log(x/y)-1`, the exact connection is

\[
G(p,q)=\sum_i p_i\,IS(q_i,p_i).
\]

If `m=sum p`, `r=sum q`, and hats denote normalization, the reused projective
identity becomes

\[
G(p,q)=m\,G(\widehat p,\widehat q)+m\,IS(r,m).
\]

The reversed arguments and source-mass weights are part of the theorem.

### 2. Exponential families and the actual log-partition

For the existing finite scalar family with a positive fixed probability
reference `q`, set `p_theta(i)=q_i exp(theta T_i)/Z(theta)` and
`psi(theta)=log Z(theta)`. Native weighted log-sum-exp calculus now proves

\[
\psi'(\theta)=E_\theta[T],\qquad
\psi''(\theta)=\operatorname{Var}_\theta(T),\qquad
D(p_\theta\|p_\eta)=B_\psi(\eta,\theta).
\]

The previous derivative/mean compatibility premise is discharged. A constant
statistic can have zero variance; the result does not assert identifiability,
strict convexity, or a globally invertible dual-coordinate chart.

### 3. Covariance scale and determinant-one shape

For real SPD covariance matrices `X,Y`, the actual centered Gaussian measures
satisfy

\[
D(\mathcal N(0,X)\|\mathcal N(0,Y))
=\frac12\left[\operatorname{tr}(Y^{-1}X)
 -\log\det(Y^{-1}X)-n\right].
\]

Whitening and an orthogonal spectral decomposition establish this without a
commutation premise on `X,Y`. The diagonal law is derived by real affine maps
of independent real Gaussians. The real expression is proved nonnegative
before removing `ENNReal.ofReal` clipping. Covariances must be strictly
positive definite; singular covariances and unequal means are outside this
evaluation theorem.

For `n>0`, put `R=Y^{-1}X`, `s=exp(log(det R)/n)`, and `S=s^{-1}R`. Then

\[
\det S=1,\qquad
\operatorname{Stein}(X,Y)
=n(s-1-\log s)+s(\operatorname{tr}S-n).
\]

Both contributions are nonnegative. `R` and `S` may be nonsymmetric; their
trace bound is proved by realizing `S` as the relative matrix of the scaled
SPD source `s^{-1}X` against `Y`. This is covariance scale. It is distinct from
the total probability-mass scale in the preceding projective identity.

### 4. Full relative modular operator and operator IS

For strictly positive real symmetric or complex Hermitian matrices `rho,sigma`,
column vectorization gives the actual Hilbert--Schmidt operator

\[
\Delta_{\sigma\mid\rho}(X)=\sigma X\rho^{-1},\qquad
[\Delta_{\sigma\mid\rho}]=(\rho^{-1})^T\otimes\sigma.
\]

Positivity follows from the matrix Kronecker product. The commuting left and
right multiplication generators give the native CFC logarithm

\[
(\log\Delta_{\sigma\mid\rho})(X)
=(\log\sigma)X-X\log\rho.
\]

The commutation here is between left and right multiplication on the full
matrix carrier; no commutation of the states is imposed. With
`Omega_rho=vec(sqrt rho)`, the proved vector expectations are

\[
\langle\Omega_\rho,\Omega_\rho\rangle=\operatorname{tr}\rho,
\quad
\langle\Omega_\rho,\Delta_{\sigma\mid\rho}\Omega_\rho\rangle
=\operatorname{tr}\sigma,
\]

\[
-\langle\Omega_\rho,(\log\Delta_{\sigma\mid\rho})\Omega_\rho\rangle
=\operatorname{tr}[\rho(\log\rho-\log\sigma)].
\]

Functional calculus lifts `x-1-log x >= 0` to the positive operator
`Delta-1-log Delta`. Its expectation is the relative-log trace plus
`trace sigma-trace rho`; the correction cancels for trace-one states.
The compatibility theorem identifies this kernel with the existing
`ArakiItakuraSaitoEquivalence.operatorItakuraSaito`, instantiated at the
constructed modular operator and its actual CFC logarithm.

### 5. Jaynes reference states and generalized thermal balance

The prior generalized Gibbs owner represents a real parameter vector by
`K(beta)=sum beta_a Q_a` and constructs `sigma_beta=exp(-K)/Z`. The new consumer
uses that same state as the reference and proves

\[
\sum_a\beta_a\left(\langle Q_a\rangle_\rho
 -\langle Q_a\rangle_{\sigma_\beta}\right)
=S(\rho)-S(\sigma_\beta)
 +\langle\Omega_\rho,
   (\Delta_{\sigma_\beta\mid\rho}-1-\log\Delta_{\sigma_\beta\mid\rho})
   \Omega_\rho\rangle.
\]

For complex matrices the equation takes the real part of the expectation.
The nonnegative defect is now a constructed operator expectation. This is an
endpoint entropy/charge balance; a controlled heat cycle or erasure protocol
still requires its own dynamical and reservoir hypotheses.

### 6. Existing graded and Jacobian structures

The paired trace/supertrace decomposition and ordered Schur factorization
remain in their existing owners. They describe different mathematical objects
from probability-mass normalization and covariance normalization. The new
proofs do not identify those three scales with each other or with a spacetime
Weyl gauge without an explicit representation and compatibility theorem.

The already proved determinant/Pfaffian/Berezinian readouts retain their
existing coefficient, skew-symmetry, block, and invertibility conditions. A
finite associative-ring Schur factorization alone does not establish a
general supermanifold or an infinite-dimensional modular standard form.

## Implemented owners and main declarations

| Owner | Main connection |
|---|---|
| `InformationGeometry.PositiveMeasureDifferential` | `hasDerivAt_generalizedKL`, `hasDerivAt_deriv_sum_gklTerm_affine`, `generalizedKL_projective_isDivergence_decomposition` |
| `ExponentialFamily.FiniteAnalyticKL` | `hasDerivAt_familyLogPartition`, `KLParam_eq_bregman`, `secondDeriv_familyLogPartition_eq_variance` |
| `Probability.KullbackLeiblerProduct` | `klDiv_map_eq_of_comp`, `klDiv_prod_eq_add`, `klDiv_pi_eq_sum` |
| `Probability.GaussianKullbackLeibler` | `multivariateGaussian_diagonal_eq_pi`, `klDiv_multivariateGaussian_zero` |
| `Probability.GaussianTraceLogdet` | `relative_covariance_trace_logdet_nonneg`, `toReal_klDiv_multivariateGaussian_zero` |
| `Jordan.BurgStein` | `det_relativeShape`, `steinLoss_scale_shape_split` |
| `Canonical.GaussianBurgStein` | `steinLoss_nonneg`, `relativeShape_trace_ge_dim`, `toReal_klDiv_gaussian_scale_shape` |
| `Canonical.MatrixRelativeModular` | `log_relativeModularMatrix`, `squareRootExpectation_itakuraSaito_eq_relativeLogTrace`, `real_relativeLogTrace_nonneg` |
| `Canonical.MatrixRelativeModularPhysicsBridge` | existing finite-action and operator-IS compatibility; `gibbs_charge_entropy_balance_modular` |

The canonical import surface `InfoGeometry.All` registers the four terminal
owners that bring in all nine selected modules. Validation results and
independent review dispositions are recorded separately in the accompanying
verification record after final acceptance.
