# Aitchison projection of a positive contingency table

## Source and formalized result

Source: M. I. Ortego and J. J. Egozcue, *Bayesian Estimation of the Orthogonal
Decomposition of a Contingency Table*, Austrian Journal of Statistics 45(4),
45–56 (2016), DOI <https://doi.org/10.17713/ajs.v45i4.136>.
The task uses the user-supplied PDF and the current source at upstream commit
`fea96b564201654cd4693008585039a56f66adf3`.

The main theorem is finite and real: the geometric-marginal independent
probability table is the unique closest independent positive probability
table for squared Aitchison distance. The interaction is the orthogonal
two-way centered log matrix. Its subspace dimension is established through
actual native linear algebra, rather than asserted by a parameter count.

This is an extension of existing owners. It does not import the separate
experimental RadonColumn development or publish the user's measured spectra.

## Existing owners and conventions

- `InfoGeometry.Probability.BipartiteLogCoupling` owns `average`, `center`,
  `interaction`, `four_term_split`, `six_orthogonal_pairs`,
  `complementary_average`, `interaction_shift`, `log_scaling_invariant`, and
  `log_product_zero`.
- `InfoGeometry.Convex.LogSumExp` owns generic finite normalized exponentials,
  the exponential partition sum, and uniform-shift invariance.
- `InfoGeometry.Probability.AitchisonFinite` owns a Fin-indexed strictly
  positive simplex and the inverse CLR/softmax identities.
- `InfoGeometry.Physics.AitchisonCLRSimplex` already proves a Fin-indexed CLR
  distance/log-ratio identity and perturbation compatibility.
- `InfoGeometry.Probability.SimplexPairingAmplitude` uses Mathlib's native
  standard simplex on arbitrary finite types and constructs independent product
  distributions.

The new result uses finite nonempty row and column index types, real matrices,
and native linear maps/submodules. Probability tables use the current native
`StdSimplex` API with a separate strict-positivity hypothesis. No additional
simplex carrier or replacement centering operator is needed.

In the current Mathlib this carrier is `Convexity.StdSimplex`; its weights are
nonnegative and finitely supported, with total one. Helper definitions using
`Real.log` are total Lean functions on that carrier. At a zero weight their
values are an algebraic extension, not ordinary CLR coordinates or geometric
marginals. The main closest-product-table theorems retain strict positivity
of the input and both competitor factors.

Write `A_I` for the existing averaging matrix and `C_I = 1 - A_I`. For a real
matrix `X`, the existing interaction is `C_I * X * C_J`. The four components
are the grand constant, centered row effect, centered column effect, and
interaction. In CLR coordinates the grand constant is zero.

For `L_ij = log P_ij`, write `r_i` for the arithmetic mean of row `i` of
`L`, `c_j` for the arithmetic mean of column `j`, and `g` for the grand
mean. The intended normalized independent projection is

```text
a_i = exp(r_i) / sum_k exp(r_k)
b_j = exp(c_j) / sum_l exp(c_l)
Q_ij = a_i * b_j
clr(Q)_ij = r_i + c_j - 2*g
E_ij = L_ij - r_i - c_j + g
clr(P) = clr(Q) + E.
```

For strictly positive `P`, the new reconstruction theorem also proves the
identity of probability tables

```text
P = softmax(clr(Q) + E).
```

This is normalized multiplicative reconstruction. Unlike the globally centered
log identity alone, this probability-table equality requires positivity. It
supplies the probability-to-coordinate step used by the closest-table proof.

Here `a` and `b` are the closed geometric marginals. The distance convention
is the **sum**, not the average, of squared CLR differences. For every
strictly positive normalized independent table `R`, the acceptance theorem is

```text
d_A(P, R)^2 = sum_ij E_ij^2 + d_A(Q, R)^2.
```

Uniqueness concerns `Q` as a probability table. An unconstrained additive
representation `u_i + v_j` retains the gauge `(u+t, v-t)`.

## Proof chain

1. Establish projection identities for the existing interaction map and
   identify its image and kernel through proved conditions.
2. Prove the squared-distance Pythagorean identity against an arbitrary
   additive row/column competitor, and derive minimality and uniqueness.
3. Identify the exponentiated, normalized additive projection with the product
   of closed geometric marginals; transfer the distance result to positive
   probability tables.
4. Construct the linear-algebra maps needed to prove the interaction and
   independence dimensions. In the full matrix space the additive kernel has
   dimension `m + n - 1`; after removing the grand constant its dimension is
   `m + n - 2`. The interaction dimension is `(m - 1) * (n - 1)`.
5. Compile the exact new declarations against the unchanged pinned toolchain
   and dependencies, inspect their axiom dependencies, and perform independent
   semantic review. The focused native and semantic checks passed at the
   source identities recorded in the validation report; the separate root
   package check is blocked by a missing dependency.

## Corrections to the source paper

The PDF is a mathematical source, not an authority for unverified statements.

| Location | Printed claim | Correction used in this task |
| --- | --- | --- |
| p. 47, before Eq. (1) | Independence subspace has dimension `(I-1)(J-1)` | Centered independence has dimension `I+J-2`; `(I-1)(J-1)` belongs to interaction. |
| p. 48, after Eq. (4) | The displayed coefficients provide `IJ+I+J-3` free parameters | The interaction has zero row and column sums, not merely a zero total; the positive probability table has `IJ-1` degrees of freedom. |
| pp. 48–49, posterior description and Eq. (7) | Posterior parameters are written `p_ij+a_ij`, and the displayed density retains the prior Gamma normalizer | The Dirichlet posterior parameters are `alpha_ij = n_ij+a_ij`; its density in probability coordinates has normalizer `Gamma(sum alpha)/product Gamma(alpha)`. |
| p. 48, interaction-sign interpretation; repeated on p. 52 | A positive interaction is interpreted as `P_ij > Q_ij` | It means a positive **centered log ratio**; the raw probability comparison does not follow. |
| p. 49, Eq. (9) | Chi-square degrees of freedom are `IJ+I+J-3` | The ordinary fixed interior multinomial null has `IJ-1`; composite independence has `(I-1)(J-1)`, with the usual regularity conditions. A posterior-drawn null needs separate calibration. |

An exact counterexample to the raw-probability sign claim is

```text
H = [[2, 4, 1/8], [1/2, 1/4, 8]]
P = [[16, 32, 1], [4, 2, 64]] / 119.
```

Every row and column product of `H` is one. Thus `E = log H`, and the
independent geometric projection of `P` is the uniform table `Q_ij = 1/6`.
Nevertheless, `E_11 = log 2 > 0` while `P_11 = 16/119 < 1/6`, since
`96 < 119`. This is exact mathematical review evidence; it is not presented
as a compiled Lean counterexample unless a corresponding theorem is added
and audited.

The posterior-density correction is a mathematical review item. It is not a
claim that conjugacy, the simplex reference measure, transformed-coordinate
Jacobians, Monte Carlo validity, or asymptotic calibration has been formalized.
The relative-deviance formula also needs a positive denominator: the uniform
table gives zero total CLR energy. Equation (10)'s average of probit-transformed
p-values has no generic uniformity theorem merely from marginally uniform
inputs. These statistical and boundary questions remain outside the finite
orthogonal-projection result.

## Boundaries

The task does not identify intrinsic detector efficiency or absolute sample
activity, prove a statistical noise model for fitted spectral areas, or prove
general Sinkhorn convergence. Arithmetic Sinkhorn marginals and geometric
orthogonal projection remain distinct operations.

The source's Bayesian section concerns multinomial counts and positive
Dirichlet parameters. Background-subtracted decimal peak areas do not inherit
that sampling model from the geometric decomposition alone.

## Connection to intensity balancing

For a positive intensity matrix `M`, the log interaction
`E = interaction (fun i j => log (M i j))` is unchanged by positive row and
column gains. This is already established by the reused
`BipartiteLogCoupling.log_scaling_invariant` theorem. Exponentiating the
zero-row/column-sum interaction yields a matrix whose row and column
**geometric** means are one.

Sinkhorn normalization selects a diagonal rescaling by prescribing
**arithmetic** row and column sums. The centered log interaction is invariant
under such a positive rescaling, but the two normalization conditions are
different. The new squared-distance theorem identifies the geometric
least-squares independent fit; it supplies no convergence rate for a
Sinkhorn iteration and no Poisson or multinomial maximum-likelihood claim.

In a spectral application, the row factor can absorb line yields, energy
response, and other row-dependent gains; the column factor can absorb
activity, exposure, load, and other column-dependent gains. A mathematical
separation into these factors does not separately identify the physical
terms inside each factor. The invariant interaction describes departures
from a separable row/column model.

## Validation record

The mathematical sources use namespace
`InfoGeometry.Probability.AitchisonContingency`.

| Source | Directly written declarations | Main contract declarations |
| --- | ---: | --- |
| `lean/InfoGeometry/Probability/AitchisonContingency.lean` | 12 definitions, 36 theorems | `interaction_idempotent`, `interaction_self_adjoint`, `mem_additiveSubspace_iff`, `mem_interactionSubspace_iff`, `additive_pythagorean`, `additive_best_approximation_eq_iff` |
| `lean/InfoGeometry/Probability/AitchisonContingencyDimensions.lean` | 2 definitions, 12 theorems/lemmas | `finrank_interactionSubspace`, `finrank_additiveSubspace`, `finrank_centeredAdditiveSubspace`, `finrank_centeredSubspace` |
| `lean/InfoGeometry/Probability/AitchisonContingencyProbability.lean` | 9 definitions, 30 theorems | `softmaxSimplex_clr`, `clr_injective`, `clr_independentProjection`, `independent_interaction_reconstruction`, `independent_pythagorean`, `independent_best_approximation`, `independent_best_approximation_eq_iff`, `projection_residual_sq` |

The total is 23 definitions and 78 directly written theorem/lemma declarations.
These source counts are distinct from the native audit's count, which also
includes private and generated constants.

`AitchisonContingencyAudit.lean` requires the named acceptance declarations and
examines every declaration in the three new owners and three reused repository
owners. `InfoGeometry.All` imports that audit to expose the complete new family.
The portable focused verifier is `verification/aitchison-contingency/check.py`;
its adjacent README documents exact-source and dependency-provenance checks.

Final commands, native audit output, hashes, independent semantic dispositions,
and the separate root-package build result are recorded in
`docs/AITCHISON_CONTINGENCY_VALIDATION.md`. Focused native verification is not
reported as a whole-repository build.
