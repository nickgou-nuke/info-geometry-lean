# Finite robust log transport

The maintained owners are `Probability/FiniteLogTransport.lean` and
`Probability/FiniteMedianShift.lean`. `InfoGeometry.All` imports the transport
owner, which imports the existing finite Aitchison owner. The dedicated audit
is `Probability/FiniteLogTransportAudit.lean`.

For an energy-by-distance matrix of positive restored observations, the method
centers each energy's logarithms across **all** distances. Each column then
uses an L1 median across energies, and these column shifts are centered again.
There is no selected reference distance. Restored observations retain their
measured residuals; the exact separability theorem concerns the mathematical
model, not a claim of perfect empirical fit.

## Proved scope

- Arbitrary finite numbers of distances and energies, with nonempty hypotheses
  where required for exact identification.
- Zero-sum centered shifts, product-one exponential scales, and uniqueness
  of the uniform translation achieving zero sum.
- Identification with the existing finite simplex CLR coordinates.
- Positive channel multipliers cancel; per-spectrum multiplicative changes
  become centered additive shifts in the log rows.
- Transport retains exactly the estimated residual, and gives the geometric
  mean scale under separability.
- Existence of a global L1 minimizer, proved by compact minimization with an
  explicit extension to all real candidates.
- Translation equivariance of the **set** of L1 minimizers.
- Sharp robustness: if a strict majority of deviations lie in
  `[theta-delta, theta+delta]`, every minimizer lies in that interval, regardless
  of all remaining values.
- The actual chosen median estimator recovers separable spectral scales.
- Centering a uniformly bounded shift error increases the bound by at most two.

`median` uses a classical choice of L1 minimizer. This is a mathematical
estimator, not an executable sorted-array implementation. In even samples,
the minimizer can be nonunique; no specific tie-breaking convention is
asserted. The robustness theorem applies to every minimizer.

The method fixes the per-energy **mean-log** baseline. It does not assert that
alternating row/column median polish finds a global joint optimum. It does not
prove a numerical precision gain, a photon-focusing law, or detector dynamics.

## Reproduction

```bash
python3 scripts/verify_finite_log_transport.py
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Probability.FiniteLogTransportAudit InfoGeometry.All
python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/Probability/FiniteLogTransport.lean lean/InfoGeometry/Probability/FiniteMedianShift.lean --fail-on warning
```

The SymPy script checks finite algebraic instances, not the general or median
theorems. Lean is the proof authority. The audit prints the axiom dependencies
of all 25 theorems in the two owners.

## Verification on 2026-09-07

The locked audit plus `InfoGeometry.All` build completed successfully (14,645
jobs, exit 0). All 25 new theorem audits report only `propext`,
`Classical.choice`, and `Quot.sound`. The new owners have no Lean warnings or
unproved placeholders. The aggregate build emits existing dependency-manifest
and unrelated module linter warnings; this is not a warning-free repository
certification. The semantic-vacuity check reports zero findings.
