# Cutoff comparison estimates and the continuum-limit endpoint

## Current destination verification — 2026-11-25

The unchanged Lean sources passed the destination-pin build and fresh audit
in [run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500),
job `139058006434`, at preparation source
`ff8e1632b45569d88da1c73c0ec160c913fe55f9`, on upstream
`c25e77e9654a54fc5e4a04bfb637b7144defacc0`. All 16 expected reports passed
the foundational-axiom check; source hashes and dependency pins matched.
Earlier validation records below retain their original scope and provenance.


This contribution formalizes the analytic steps linking consecutive-cutoff
comparison estimates to convergence of normalized observables in Section 11
of `Continuum Limit Manuscripts/WILSON_LOOPS_CONTINUUM_LIMIT.tex`.

The files use native Mathlib functions and predicates: complex division and
norms, finite sums and maxima, monotonicity, real powers and logarithms,
`Asymptotics.IsBigO`, `Summable`, `CauchySeq`, and `Filter.Tendsto`.
They introduce no custom convergence or positivity certificates.

## Theorem contracts

| Module | Proved conclusion | Explicit inputs |
| --- | --- | --- |
| `CoreLean.CutoffComparison` | Exact normalized ratio difference; norm bound `εN + B * εZ`; scalar exponential normalization error; full-sequence convergence with a tail sum | Positive physical denominators, relative numerator and denominator errors, a bound `B` on the new normalized observable, summability of the relative errors for the generic endpoint |
| `CoreLean.CutoffRecursion` | `u i ≤ C / (1 - θ) * w i`; at weighted contraction `1/4`, the manuscript's bound `2 * C * w i` | Finite index set, nonnegative `u`, positive weights, `u ≤ T u + s`, `s ≤ C w`, `θ < 1`, and the displayed weighted estimate for `T` |
| `CoreLean.CutoffSummability` | Summability of `K^(3-κ/2) * log(b*K+c)^p`, including multiplication by `K` | `κ ≥ 13`, `b > 0`, `c ≥ 0`, fixed real exponent `p ≥ 0` |
| `CoreLean.CutoffLimit` | Full normalized-sequence convergence, with tail constant `CN + B * CZ` and the explicit logarithmic remainder | The preceding numerical conditions plus the two displayed relative comparison inequalities for actual `N` and `Z` |
| `CoreLean.CutoffCheck` | Printed dependency audit for every public theorem | The four proof modules |

### Physical normalization

For complex numerators and positive real partition functions, the exact
identity is

\[
 \frac{N'}{Z'}-\frac N Z
 =\frac{(N'-N)-(N'/Z')(Z'-Z)}{Z}.
\]

If `‖N' − N‖ ≤ εN * Z`, `|Z' − Z| ≤ εZ * Z`, and
`‖N'/Z'‖ ≤ B`, then

\[
 \left\lVert\frac{N'}{Z'}-\frac N Z\right\rVert
 \le \varepsilon_N+B\varepsilon_Z.
\]

The denominator remains the physical partition function. No uniform positive
lower bound on partition functions is assumed: both errors are relative to
the same old positive denominator. The numerator can include perimeter and
corner normalization factors.

The separate scalar estimate
`‖exp z * w − w‖ ≤ (exp δ − 1) * B`, for `‖z‖ ≤ δ` and `‖w‖ ≤ B`,
handles a change of those factors when a bound on their exponent difference
is available.

### Finite recursion

`le_weight_of_monotone_homogeneous` treats the manuscript's nonlinear
monotone, positively homogeneous operator directly. Both properties are
required only on the nonnegative cone. It assumes the estimate
`T w ≤ θ w` only at the weight, and derives the desired estimate on `u`.
The proof constructs a maximizing index for the finite family `u i / w i`
and obtains `M ≤ θ * M + C`. It also covers an empty index type without an
extra nonemptiness assumption.

`le_weight_of_row_bound` specializes this argument to the concrete operator
`T v i = ∑ j, A i j * v j`. Nonnegative matrix entries establish
monotonicity, finite-sum algebra establishes homogeneity, and the weighted
row sums provide `T w ≤ θ w`.

The RG application uses `w i = i * thetaTilde^i + wK`. Its positivity,
the uniform weighted kernel estimate, and the source estimates remain to be
proved from the actual two-run recursion. The current files do not assert
these physical estimates.

### Summability and cutoff limit

The general summability lemma proves

\[
 \sum_{K=0}^{\infty}K^a\bigl(\log(bK+c)\bigr)^p
 \quad\text{is summable when }a<-1,
\]

for `b > 0`, `c ≥ 0`, and real `p ≥ 0`. The logarithmic power uses native
`Real.rpow`. The proof applies Mathlib's `Asymptotics.IsBigO.rpow` and
`isLittleO_log_rpow_rpow_atTop` to absorb the log power into `K^δ`, with
`δ = (-1-a)/2`, then uses Mathlib's real p-series theorem. Natural-power
corollaries are retained via `Real.rpow_natCast`. The finitely many values
before the logarithm becomes positive, including `K = 0`, have no effect
on summability.

The manuscript specialization takes `c = gbar⁻²` and `p = 4*r + 2*p0`
directly as a real exponent. Appendix `app:constants`, Stage 0, fixes `r = 2`
and bounds `p0` below but does not require it to be an integer. Thus the
real-exponent contract avoids an extra integrality hypothesis; its
nonnegativity follows from the stated lower bounds. The two resulting power exponents are
`3 − κ/2` and `4 − κ/2`. In fact, the summability proofs respectively need
only `κ > 8` and `κ > 10`; the stated manuscript condition `κ ≥ 13`
satisfies both with a strict margin.

Let

\[
 e_K=K\,K^{3-\kappa/2}\bigl(\log(bK+c)\bigr)^p.
\]

For a fixed admissible starting cutoff `K0`, the final theorem uses

\[
 \begin{aligned}
 \lVert N_{K+1}-N_K\rVert&\le C_N e_K Z_K,\\
 |Z_{K+1}-Z_K|&\le C_Z e_K Z_K,\\
 \lVert N_{K+1}/Z_{K+1}\rVert&\le B,
 \end{aligned}
 \qquad K\ge K_0.
\]

It proves convergence of the full sequence `N K / Z K` to a complex number
`limit`, with the explicit estimate

\[
 \left\lVert\frac{N_{K_0+k}}{Z_{K_0+k}}-\mathrm{limit}\right\rVert
 \le (C_N+B C_Z)\sum_{j=0}^{\infty}e_{K_0+k+j}.
\]

The Cauchy and tail steps use Mathlib's
`cauchySeq_of_dist_le_of_summable` and
`dist_le_tsum_of_dist_le_of_tendsto`; finite initial cutoffs are removed by
`Filter.tendsto_add_atTop_iff_nat`.

## Scope and integration

The manuscript also contains geometric depth terms, insertion remainders,
and sums over paired backgrounds. The generic relative-error endpoint can
combine any such terms after their summability and relative error bounds
have been proved. The explicit logarithmic specialization covers the
polynomial-logarithmic error and its linear loss; it does not claim to
derive every summand of the manuscript's complete error profile.

These files do not establish gauge-theory correlation estimates, construct
the Wilson measure, prove the RG row bounds, identify an inductive colimit
with a continuum probability measure, or settle a physical continuum-limit
theorem. They discharge concrete finite-dimensional and analytic steps
that such a theorem requires.

Existing `ComparisonArith` supplies local mean-value and lattice summation
estimates. `ChainConditionsArith.power_log_tendsto` supplies decay of a
specific real function. The present modules add normalized-denominator
comparison, a finite weighted recursion solution, actual summability,
and a full-sequence endpoint; they do not replace those existing owners.

## Verification

From `LEAN/CoreLean`, compile the four modules in dependency order and run
the axiom audit:

```sh
lake --wfail build CoreLean.CutoffRecursion CoreLean.CutoffComparison CoreLean.CutoffSummability CoreLean.CutoffLimit
lake env lean CoreLean/CutoffCheck.lean
```

The target repository's pinned Lean and Mathlib versions remain authoritative;
the build treats warnings as failures.

All five sources passed exact destination Lean 4.36.0 with Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, run `45458690593`,
job `138675000638`, preparation commit `0d848bd531f595d8cac0e06b13dad2e48fca8132`. The warnings-as-errors
build, separate fresh 16-declaration axiom audit, source hashes and unchanged
dependency-pin checks all passed. The reports use only `propext`,
`Classical.choice`, and `Quot.sound`.

The parent independently matched every current Lean source hash to the
successful artifact in `validation/evidence/exact-cutoff-0d848bd`.
The nonlinear maximum theorem uses `Finite` and chooses an enumeration
inside its proof. The header linter remains enabled with the separate
Apache notice text. Independent review confirmed that the cone hypotheses,
physical denominator, real logarithmic exponent and tail constants remain
unchanged by the destination compatibility repairs.
