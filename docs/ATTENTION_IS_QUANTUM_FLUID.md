# Finite Softmax Information Geometry: Verified Boundary

## Scope correction

The earlier title and narrative identified transformer attention with a KMS
state and a divergence-free quantum fluid. The cited finite calculations and
Lean equalities do not establish those identifications. They establish a
finite Gibbs/softmax model, its log-partition calculus, and several separate
linear-algebra facts. This note preserves those valid results and marks the
missing structures explicitly.

## The finite exponential-family chain

For a nonempty finite index type `Fin M` and logits `s : Fin M → ℝ`, define

\[
Z(s)=\sum_j e^{s_j},\qquad \psi(s)=\log Z(s),\qquad
p_s(j)=e^{s_j}/Z(s).
\]

The weights are strictly positive and sum to one. Varying coordinate `j` gives
the first derivative

\[
\partial_j\psi(s)=p_s(j).
\]

For token indicators `O_j(m)=1` when `m=j` and zero otherwise, the second
coordinate derivative is

\[
\partial_k\partial_j\psi(s)
 =\mathbf 1_{j=k}p_s(j)-p_s(j)p_s(k)
 =\operatorname{Cov}_{p_s}(O_j,O_k).
\]

Thus the Hessian is the covariance matrix and the Fisher information matrix
for this finite categorical exponential family. For any direction `v`,

\[
v^T\nabla^2\psi(s)v
 =\sum_m p_s(m)(v_m-\mathbb E_{p_s}v)^2\ge 0.
\]

Because every `p_s(m)` is positive, this is zero exactly when `v` is
constant. Equivalently, `ψ` is strictly curved on the quotient by the
constant-logit direction; it is not strictly convex on all of `ℝ^M`.
Adding a constant `c` to every logit leaves `p_s` unchanged and adds `c` to
`ψ(s)`.

Lean owners:

- `InfoGeometry.Analytic.LogSumExp` provides finite weighted log-sum-exp
  derivatives, centered variance, and common-weight scaling.
- `InfoGeometry.Canonical.AttentionInformationGeometry` proves the softmax
  coordinate derivatives, the actual mixed second derivatives, their
  covariance/Fisher identities, the variance quadratic form, positive
  semidefiniteness, strict positivity in nonconstant directions, and shift
  invariance.

## Gibbs form and zero-temperature routing

For scores `s`, the same distribution is a finite Gibbs law with energy
`E_j=-s_j` and inverse temperature `β=1`. More generally, logits `β s_j`
give energy `-s_j` at inverse temperature `β`. This is an equality of finite
probability weights and partition functions.

For a finite score vector with a unique strict maximizer, softmax at inverse
temperature `β→+∞` converges to the point mass at that maximizer. If there are
several maximizers, the limit is uniform on the maximizing set, not a single
argmax point mass.

Lean owners:

- `InfoGeometry.Routing.FiniteSoftmax` identifies softmax weights with the
  existing finite Gibbs model and proves the unique-maximum limit.
- `InfoGeometry.Canonical.DeterministicArgmaxAttention` lifts the pointwise
  result to finite matrix convergence for rowwise unique maxima.
- `InfoGeometry.Inference.FiniteGibbsZeroTemperature` contains the more general
  finite energy-gap and tied-ground-state results.

## Mutual information and independence

Given a finite joint law `P(i,j)` and its marginals `p(i)` and `q(j)`, the
dependence ratio is

\[
r(i,j)=P(i,j)/(p(i)q(j)),
\]
where the denominator is positive on the support under the strict-positivity
hypotheses. Shannon mutual information is the finite relative entropy
`D(P ‖ p⊗q)`, hence is nonnegative and equals zero exactly at independence.
For the repository's uniform-query attention law, independence is equivalently
the equality of every attention row with the key marginal.

This ratio is a probability-theoretic density ratio. Calling it the optical
Glauber correlation `g⁽²⁾`, or identifying a transformer attention matrix with
a quantum-optical correlator, requires a separate model and theorem. The
finite identity alone does not supply that interpretation.

Lean owner: `InfoGeometry.Canonical.AttentionGlauberCopulaBridge` proves the
finite entropy identity, the relative-entropy representation, nonnegativity,
and the zero-information iff independence result.

## Distinct facts that do not follow from softmax

1. A probability vector of Gibbs form is not by itself a KMS state. A KMS
   statement requires an observable algebra, a specified time-evolution
   automorphism group, and the KMS boundary condition for a state on that
   algebra. The repository's finite diagonal model proves a detailed-balance
   identity for its explicitly defined modular shift; the router weight
   equality alone does not identify a runtime transformer with that KMS model.
2. For a differentiable linear vector field `u(x)=Ax`, its divergence is
   `trace(A)`. A skew-symmetric real matrix has trace zero, so this particular
   linear field is divergence-free. This fact does not turn softmax weights,
   an attention Jacobian, or a Clifford operator into a fluid velocity field.
3. Numerical CAS output can check finite examples. It is not a proof of a
   general theorem, a hydrodynamic limit, a training/inference phase transition,
   unitarity, or a physical model of a named commercial transformer.

These are the exact boundaries: finite exponential-family calculus and finite
Gibbs identities are formalized; the KMS, quantum-optical, and fluid
identifications remain separate development obligations unless their carriers
and maps are explicitly defined and proved.
