# Spectral table factorization: theorem and publication contract

## Intent and provenance

This change integrates the verified spectral-table development at the user's
request to publish a pull request. The upstream base inspected is
`fea96b564201654cd4693008585039a56f66adf3`. Dependency pins are unchanged:
Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The source package is `Spectral_Table_Bridge_20261119.zip`, SHA-256
`3bdd0a29ccf24aba273b2b4ea07ce33044cb3ee44e5ebbf2fd9db0f1e7d49207`.
Its complete prose intakes remain preserved with that source artifact. This
PR carries selected mathematical owners and compact measurement fixtures;
it does not republish the complete conversations or change the transport
models in the separate radon PR409.

The decimal five-channel CSV has SHA-256
`30a4bc1781ebade1636f74fe3703faea04d5584d72b4a178cc84f4bd11e6fa6d`.
The rounded two-line fixture is extracted from the published intake with
SHA-256 `882b6799b2787041c86e07b36c7fe892ee1e7807756e05273227ac73b9411754`.
Its extraction and correspondence are recorded with the fixture. Decimal
net areas and rounded areas are distinct inputs. Numerical enclosures treat
those entered values exactly and are not measurement uncertainty intervals.

## Carrier and conventions

- Arbitrary finite real rectangular tables, equivalently native `Matrix I J ℝ`.
- Samples are rows and spectral channels are columns. Transposition connects
  the earlier line-by-sample convention explicitly.
- Logarithms of measured rates require positive entries in a fixed reference
  unit. Pure log-table identities accept arbitrary real entries.
- Uniform finite means define geometric factors; fixed positive arithmetic
  targets define the Sinkhorn updates. The two operations are distinct.
- Sample corrections add one log scalar per sample. Row-first iteration uses
  an arbitrary shared initial column potential and arbitrary target log
  margins. Feasible simultaneous balancing additionally needs equal total
  target masses; finite covariance does not assert convergence.
- No complex carrier, operator-algebra interpretation, physical cause, or
  absolute detector-efficiency identification is introduced.

## Existing owners inspected

The owner search covered `lean/` and `src/`, imported definitions and consumers,
and the current Lake/tooling entrypoints. External references and graph tools
are navigation surfaces, not proof authority. No refreshed declaration graph
or whole-repository absence claim is made.

| Existing owner | Reused or distinguished scope |
|---|---|
| `Probability.BipartiteLogCoupling` | Actual rectangular centering matrices, four-term split, six orthogonal pairs, and log-scaling invariance. The new entrywise/matrix equality connects directly to this owner. |
| `Spectrometry.SvdClrEquivalence` | Positive factorization, additive log/common CLR equivalences, native outer products and geometric normalization on `Fin` dimensions. Native `Matrix.vecMulVec` is used directly in the new table owner. |
| `Routing.FiniteLogSinkhorn` | Square, zero-initialized, unit-row/column updates. The new rectangular arbitrary-target and arbitrary-initial-potential covariance has a different interface. |
| `Physics.AmariSinkhornAlternatingProjections` | Rectangular arithmetic marginal updates and normalization. General convergence is outside this change. |
| `Spectrometry.MatrixFixedScaleLeastSquares` | Fixed-scale raw-intensity least squares; distinct from the free additive log-table projection proved here. |

The existing matrix-centering owner's broad `import Mathlib` is narrowed
to focused imports without changing its mathematical declarations or proofs. This is an import-scope change, not a new centering
construction.

## Claims and dependency order

| Claim | Owner | Exact boundary |
|---|---|---|
| Positive diagonal scaling, cross-ratios, geometric means, rank-one balancing and exact LSE update | `TableBalancing` | Explicit positivity/nonzero hypotheses; outer product is native `Matrix.vecMulVec`; no general balancing convergence. |
| Double-centered interaction and additive gauge invariance | `LogInteractionAndGauge` and `MatrixLogCentering` | Actual finite operators; the matrix/entrywise bridge is proved, not assumed. |
| Global unweighted log least-squares minimizer | `LogLeastSquares` | Derives zero sums, orthogonality and Pythagorean identity. Unique fitted table; factor potentials retain opposite constant shifts. |
| Row/column orientation and finite Sinkhorn covariance | `ColumnFirstSinkhornCovariance`, `SpectralOrientation` | Actual recursive updates, half/full-step normalization and invariance; no extra potential recentering or limit claim. |
| Restriction preserves geometric contrasts and fixed-fit-set slopes | `SpectralRestriction`, `InteriorLogSlope` | The channel set, selected fit samples, predictor and weights are held fixed. Statistical slope interpretation requires suitable weights and predictor variance. |
| Restricted interaction must be recentered | `SpectralRestriction` | Exact finite identity; restriction alone generally fails the retained column-mean constraints. |
| Sinkhorn inverse-factor ratios can change on restriction | `SpectralRestriction` | Explicit strictly positive 3-by-2 and 2-by-2 balanced witnesses, with ratios 2/5 and 1/2. |
| Two-channel interaction has opposite columns and zero minors | `SpectralOrientation` | Holds for every real two-channel log table; does not identify a loading mechanism. |
| Common spatial residual is orthogonal to spectral interaction | `LogLeastSquares.interaction_orthogonal_additive` and its squared-norm decomposition | Actual unweighted finite inner product and Pythagorean identity; no calibrated significance claim. |
| Step residuals and projection-dependent energy ratios | `InteriorStepAndRatioSignatures`, `ProjectionEnergy` | Algebraic step signatures and a concrete energy-ratio counterexample; percentages depend on the projection used. |
| Exact two-line balancing and global analytic error bounds | `GlobalHyperbolicBounds`, `ExactTwoLineRoot`, `TwoLineBalancedConstruction`, `TwoLineNonasymptoticBounds` | Finite nonempty line-ratio set, explicit centering/bounds where used; not a five-channel analytic remainder theorem. |

The causal order is observation and logarithm, finite means and interaction,
orthogonality and least-squares projection, actual balancing updates,
orientation/restriction compatibility, then the spatial and two-line
diagnostics. Edges correspond to the imported definitions and proved lemmas.

## Computational evidence

The measured areas, time metadata and common start-time correction are retained.
The nominal 77-keV channel remains an unresolved ROI. No photon yield is guessed.
The analysis compares all-nine and interior-seven normalization domains,
fits both 2–8 and 4–8 intervals, and separates method agreement, interaction,
and common spatial residuals. The exact rational interval evaluator is reused
without modification; its implementation is not formally verified in Lean.

Reproduced interior five-channel values are a geometric attenuation slope of
0.654214245448 per cartridge, a Sinkhorn slope of 0.654174302068, maximum
factor difference 0.0271851%, maximum absolute log interaction 0.0525028565,
and maximum common exponential residual 6.92287%. These are deterministic
descriptive results, not evidence identifying saturation, flipping, leakage,
daughter equilibrium, or detector background.

The focused import is `InfoGeometry.Spectrometry.SpectralTableFactorization`.
The numerical entry point is `python3 tools/spectral_table_bridge/reproduce.py`;
its [README](../tools/spectral_table_bridge/README.md) records the input mapping,
normalization domains, dependency versions and reproduction commands. The
[diagnostic figure](../artifacts/spectral_table_bridge/figures/spectral_bridge_diagnostics.png)
keeps the common spatial residual separate from the spectral interaction.

## Acceptance and remaining debt

The packaged standalone verification is provenance. The integrated source has
now passed separate independent source review and execution QA. The
[validation record](../artifacts/spectral_table_bridge/verification/VALIDATION.md)
names the canonical source hashes, unchanged dependency pins, maintained-lock
commands, declaration audit and numerical reproduction. All 15 selected
declaration-bearing owners compile, and the native audit checks all 555 owned
declarations, including private/generated declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. The focused umbrella and both strict
source screens pass. The closure retains 44 nonfatal Lean linter warnings.

The actual root Lake target build exits 1 during package initialization because
`external_refs/homotopy-hypothesis-lean4` is absent. It does not reach target
elaboration. The toolchain, manifest and Lake configurations remain unchanged.
Focused acceptance therefore does not establish root integration. The installed
commit and push hooks are additional publication gates, reported in the PR.

Open claims include general rectangular Sinkhorn existence/uniqueness and
convergence, global KL projection optimality, a complete Aitchison metric-space
construction, machine-checked numerical interval evaluation, calibrated
measurement error, and physical identification of the extracted factors.
