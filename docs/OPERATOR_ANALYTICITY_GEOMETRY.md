# Analyticity and geometry for operator algebras

The repository uses “analytic” for several different structures. They share
some maps, but they are not one theorem or one interchangeable definition.
This note records the source-backed bridges and their actual scopes.

## Geometric spine

| Level | Native structure | Owner | Scope |
|---|---|---|---|
| Complex analytic orbit | `AnalyticAt ℂ` for `alpha G z B` in a `CStarAlgebra` | `OperatorAlgebra/ComplexTimeConjugation.lean` | Entire complex-time conjugation orbit for a bounded algebra element; self-adjointness is needed for the real-time unitary interpretation. |
| Phase-linear tangent | `CauchyAnalyticAt`, consisting of `HasFDerivAt` over `ℝ` and derivative intertwining of phase operators | `Geometry/BilingualAnalyticity.lean` | Pointwise differentiability and Cauchy–Riemann phase law; it does not by itself assert neighborhood holomorphy or a power series. |
| Operator orbit geometry | `alphaPhaseCauchy`, `alpha_realDerivative_phase`, and closedness of the calibrated one-form | `Canonical/ComplexOperatorBilingualAnalyticity.lean` | Converts the actual complex-analytic orbit into its real phase-linear tangent law for operator-valued targets. This is the concrete bridge between the first two levels. |
| Hestenes–Krein differential geometry | `IsHestenesHolomorphicDifferential` and `CauchyAnalyticAt` equivalence | `Canonical/HestenesAnalyticity.lean` | Identifies phase-linearity with the clock-axis/Hestenes differential on doubled real Hilbert spaces. |
| Filtered normed transport | `FilteredPhaseCone` bonding and inclusion maps with phase-intertwining laws | `Canonical/FilteredInductiveHestenesAnalyticity.lean`, `Canonical/FilteredHestenesKreinColimit.lean` | Transports actual continuous-linear derivatives through a compatible normed cone; the displayed results are stagewise and cone-level. |
| Algebraic direct-limit phase | Additive endomorphism on `AddCommGroup.DirectLimit` with square `-1` | `Analytic/HKColimitAnalyticity.lean` | Purely algebraic descent. It does not establish a normed or analytic direct-limit topology. |
| Real operator potentials | `HasFDerivAt`, higher derivatives, and `ContDiffAt ℝ` for log-determinant and quadratic log-volume | `Analysis/ComplexMatrixLogDetCalculus.lean`, `Canonical/ModularSurprisalQuadraticLogVolume.lean` | Real Fréchet calculus on full finite complex matrix algebras, with matrix-factor order retained. The real-valued log-volume is not claimed to be holomorphic as a complex-valued map. |
| Hessian/barrier geometry | Real Fréchet Hessian maps and Dikin/barrier results | `Canonical/UnifiedDikinGeometry.lean` and its focused owners | Real convex-analytic geometry under the stated norm, differentiability, and positivity hypotheses. |

## Established arrows

1. Complex analyticity implies real Fréchet differentiability and the phase
   Cauchy–Riemann law for complex normed operator spaces. The operator orbit
   specialization is `alphaPhaseCauchy` in
   `ComplexOperatorBilingualAnalyticity.lean`, now exposed through
   `Canonical/All.lean`.
2. On doubled real Hilbert carriers, the phase-linear derivative condition is
   exactly the Hestenes-holomorphic differential condition, via
   `isHestenesHolomorphicDifferential_iff_isPhaseLinearMap`.
3. Filtered normed cone maps inherit pointwise `CauchyAnalyticAt` data because
   the bonding and inclusion maps are continuous linear and phase-linear.
4. The algebraic direct-limit phase theorem is a separate transport result.
   Its carrier has no normed topology in that owner, so no analytic limit is
   inferred from it.
5. Matrix log-volume and Dikin Hessians are genuine real analysis on their
   stated finite-dimensional/operator normed carriers. Their existence does
   not imply complex holomorphy, a KMS strip theorem, or an analytic result on
   an abstract algebraic direct limit.

`Canonical/UnifiedAnalyticGeometricFramework.lean` is the existing cross-clade
synthesis owner. Its master theorem packages separately proved scalar,
finite-matrix, complex-monodromy, filtered-phase, and operator-clock claims in
a conjunction. That is useful repository-level traceability, but the product
statement does not itself prove that these carriers form one analytic space.
The operator-orbit-to-phase bridge remains the typed geometric connection;
the `Canonical/All.lean` import makes it available on the canonical umbrella.

## Explicit boundary

The useful common geometric language is “a differentiable map whose tangent
intertwines the chosen phase structure.” Complex holomorphy supplies this
property for complex-time operator orbits; Hestenes geometry identifies it
with the doubled-space clock axis; filtered normed cones transport it. The
finite-matrix log-volume and the algebraic direct-limit phase remain separate
branches until a typed map and a proved compatibility theorem connect them.

In particular, `Analytic/HKColimitAnalyticity.lean` proves descent of an
additive phase operator to an algebraic direct limit. It does not replace
`AnalyticAt`, `CauchyAnalyticAt`, or the normed filtered-cone results.
