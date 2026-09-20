# Bernoulli entropy relaxation and the Dirac-reference boundary

## Scope

`lean/InfoGeometry/Epistemology/EpistemicGradientFlow.lean` extends the existing
`Geometry.BinaryLegendreEntropyFlow` trajectory rather than defining a second
flow. For an arbitrary real initial log odds `initial`, it uses

\[
  p(t)=\operatorname{logistic}(\text{initial}\,e^{-t}),
  \qquad D(t)=\varphi(p(t))-\varphi(1/2),
\]

where `negativeEntropy` is
\(\varphi(p)=p\log p+(1-p)\log(1-p)\).
`relativeEntropy_eq_binary_kl` identifies this deficit with the sum of the
two scalar KL contributions against the fair Bernoulli distribution.
The reference distribution has full support; it is not a Dirac mass.

## Proved statements

- `logistic_quarter_lipschitz` bounds the logistic slope globally by `1/4`,
  using the native mean-value theorem and the existing Bernoulli variance bound.
- `midpoint_entropy_quadratic_bound` combines that estimate with nonnegativity
  of the reversed Fenchel gap to prove
  \(0\leq D(\operatorname{logistic}\theta)\leq\theta^2/4\).
- `hasDerivAt_relativeEntropy` differentiates the actual trajectory.
  `relativeEntropy_dissipation` rewrites the result as
  \[
    D'(t)=-g_{\mathrm{mix}}(p(t))\,[p'(t)]^2,
    \qquad g_{\mathrm{mix}}(p)=\frac1{p(1-p)}.
  \]
- `relativeEntropy_antitone` proves monotonicity of the deficit.
- `relativeEntropy_exponential_bound` proves, for all real `initial` and `time`,
  \[
    0\leq D(t)\leq\frac{\text{initial}^2}{4}e^{-2t}.
  \]
- `relaxation_tendsto_midpoint` and `relativeEntropy_tendsto_zero` prove the
  limits \(p(t)\to1/2\) and \(D(t)\to0\) as \(t\to+\infty\).

The decay estimate is derived for this explicit finite-dimensional flow. It
does not assume a logarithmic Sobolev inequality or a diffusion equation.
The initial-coordinate prefactor is not asserted to equal `D(0)`.

## Why the proposed Dirac formula cannot be used

`DiracRelativeEntropyBoundary.lean` reuses the repository's alias for Mathlib's
extended-real measure KL divergence. It proves

\[
  \rho(\{x\}^{c})\ne0
  \quad\Longrightarrow\quad
  D_{\mathrm{KL}}(\rho\parallel\delta_x)=+\infty.
\]

The proof exhibits failure of absolute continuity. A regression example gives
\(D_{\mathrm{KL}}(\delta_0\parallel\delta_1)=+\infty\).
Consequently, the supplied finite derivative formula for KL relative to a
Dirac target does not describe a general nonsingular distribution. No such
identity is inserted as an assumption or an axiom.

The trajectory studied here maximizes Bernoulli entropy at equilibrium; it
does not freeze into a Boolean state. There is no temperature parameter, no
zero-temperature concentration theorem, and no Wasserstein or Fokker–Planck
identification in these modules. The convex-hull unique-maximizer theorem in
`CrystallizedGrammar` remains a separate conditional result.

## Declared dependency poset

`EpistemicGradientFlowDependency.lean` records separate proof branches:

```text
logistic derivative + Fenchel nonnegativity -> quadratic bound
quadratic bound + explicit relaxation       -> exponential decay bound
explicit relaxation                        -> dissipation identity
explicit relaxation                        -> equilibrium limit
failure of absolute continuity             -> Dirac-reference obstruction
```

Finite prerequisite sets define a genuine partial order. The dissipation and
decay-bound nodes are incomparable in this chosen proof organization, as are
the Dirac obstruction and equilibrium-limit nodes. This is an explicit
dependency model, not extraction of Lean's environment, logical independence
of the mathematical propositions, or a causal law of cognition.

## Validation

The regression module is `EpistemicGradientFlowTests.lean`. It exercises the
decay bound, dissipation identity, both limits, and a singular-reference
counterexample; it also requests axiom reports for all fifteen new theorems.
Serial local verification uses the shared build lock, installed Lean 4.28.x,
cached Mathlib, and isolated build outputs. The repository pins Lean 4.28.1,
which is not installed locally. No dependency metadata is changed, and this
does not constitute a pinned-toolchain or full-repository build.

All five regression examples and fifteen axiom audits passed the local check.
The audits report only subsets of `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axioms occur. These are kernel-checked
Mathlib proofs, not claims of choice-free constructive analysis.
