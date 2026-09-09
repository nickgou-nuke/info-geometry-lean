# Finite detector ensemble: theorem scope

This extends the two-distance results in `DetectorScaleInvariance.lean` to a
finite ensemble without selecting a reference acquisition.

## Owners

- `Probability/FiniteLogTransport.lean`: canonical finite mean-log centering,
  CLR identification, residual-preserving transport and the actual median-based
  spectral estimator. No acquisition defines the reference.
- `Probability/FiniteMedianShift.lean`: existence of an absolute-loss minimizer,
  translation of the minimizer set, and strict-majority interval protection.
- `Probability/DetectorEnsembleTransport.lean`: extensions proving uniqueness
  of a mean-zero exact factorization, product preservation for arbitrary rows,
  and the Weyl weight-one surprisal transformation.
- `Nuclear/DetectorInformationGeometry.lean`: geometric response to the
  Massieu Hessian, binary loss-state modular frequency, and ensemble CLR
  frequencies on the distance carrier. These are separate finite index sets.
- `Nuclear/DetectorInformationGeometryAudit.lean`: integrates these owners
  with the existing simplex, barrier, Legendre, GENERIC, modular and dual-area
  audits. `Nuclear/All.lean` imports the new bridge.

## Statistical scope

The implemented primary estimator fixes each energy baseline to its mean log
rate, estimates each distance shift by a scalar median, then centers the shifts.
If viewing this as an additive factorization, compensate the energy baseline
by the opposite mean shift. `gauge_center_residual` proves residual invariance.
Centering preserves the product of every transported energy row even when
the response has residuals. Exact collapse is asserted only for rank-one data.

If a strict majority of energy deviations lies in [theta-delta,theta+delta],
every scalar absolute-loss minimizer lies in that interval. This is a location
stage guarantee, not a breakdown guarantee for the upstream TCS fit or the full
correlated pipeline. The formal estimator uses a mathematically chosen minimizer;
it does not certify NumPy, an iterative stopping rule, or a unique selection in
all tied samples. Exact separable collapse is proved for this estimator.


## Angular convention

The maintained `Probability/DetectorCrossSectionDuality.lean` now distinguishes
Wpp (peak-peak) from Wpt (peak-total). Its general recovery is

    (Pij/Pj) * Wpt * (Speak_i/Sv_j) = Wpt/(B_j*Wpp).

Wpt=1 gives 1/(B_j*Wpp); Wpt=Wpp gives 1/B_j. The earlier microscopic
decomposition without Wpt either absorbs it in the total response or uses unity.
No nuclear coefficient is assigned a numerical value by these theorems.

## Reproduction

    python3 scripts/verify_detector_ensemble.py --output scripts/verify_detector_ensemble.json
    python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Nuclear.DetectorInformationGeometryAudit InfoGeometry.All

The JSON is an exact finite-coordinate CAS cross-check; general finite proofs
are Lean source. Build status must be read from the actual command output.
Existing dependency-manifest and upstream lint warnings are separate from
new-owner errors. No full-repository clean-build claim follows from this target.

## Verified baseline — 7 September 2026

The locked integrated audit plus `InfoGeometry.All` completed successfully
(14,669 jobs, exit 0). The seven extension theorem axiom readbacks contain only
`propext`, `Classical.choice`, and `Quot.sound`; the integrated imports also run
the finite transport/median and existing simplex/duality audits.
The scoped semantic-vacuity audit reports zero; staged proof-proxy and four
owner anti-hypothesis gates pass. The CAS companions pass 9 ensemble and 14
duality identities with zero residuals. Source hashes and precise scope are in
`DETECTOR_ENSEMBLE_VERIFICATION.json`.

The shared index includes concurrent work outside this task; these additions
are staged, with no release commit or immutable tag. Existing upstream build
warnings remain. This baseline certifies the stated mathematical contracts,
not numerical activities, aperture-convergence rates, empirical improvement,
or manuscript submission readiness.
