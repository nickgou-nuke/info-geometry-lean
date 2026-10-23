# Signed-radius circle enclosure realignment

## Ground-truth contract

The counterexample `BipolarCircleEnclosurePeriods.negative_radius_exterior_counterexample`
uses Mathlib's actual circle integral: a negative-radius metric closed ball is
empty, whereas the parametrized circle still encloses its center. The constructive
replacement uses the geometric radius `|r|`, without restricting `r` to be positive.

Carriers remain `ℂ`, `ℝ`, Mathlib `circleIntegral`, and the existing
`poleEnclosureIndex`, `circleEnclosurePair`, `dlog01`, and `circulationPeriod`.
No alternative path or winding-number carrier is introduced.

Source anchors:

- Mathlib `circleMap_neg_radius`: `circleMap c (-r) x = circleMap c r (x + π)`.
- Mathlib `Function.Periodic.intervalIntegral_add_eq`: an integral over one period
  is independent of its starting point.
- `BipolarCircleEnclosurePeriods.circleIntegral_pole_eq_enclosure`: the existing
  enclosure formula assumes `0 ≤ r` and excludes the pole from `sphere c r`.
- `BipolarCircleEnclosurePeriods.circleIntegral_dlog01_eq_circulationPeriod`:
  the two-puncture period formula under the analogous nonnegative-radius hypotheses.

The source-confirmed extension is integral invariance under radius negation and
absolute value, followed by the enclosure and bipolar period formulas with
puncture avoidance on `sphere c |r|`. The radius-zero case is included whenever
the stated puncture-avoidance hypotheses hold.

Search: repository Lean sources for the counterexample, enclosure owner/imports,
and circle-map radius identities; Mathlib CircleIntegral and periodic interval
integration sources. OpenGauss discovery receipt: `/tmp/signed-radius-discovery.json`
(navigation only). Existing nonnegative-radius clients remain valid.

Not claimed: negative radius reverses orientation; poles on the contour are
regular; arbitrary loop homotopy classification; repository-wide completion.

## Verification

The locked build of `InfoGeometry.Analysis.BipolarSignedRadiusPeriodsAudit`
completed successfully (4345 jobs). All four declarations report only
`propext`, `Classical.choice`, and `Quot.sound`. The audit also compiles
negative-radius and zero-radius instances of the new enclosure formula.
There are no warnings in the two new Lean files; the build replays dependency
warnings (182 warning lines in `/tmp/signed-radius-audit.log`).

The strict OpenGauss screens for both new Lean files report zero traps.
Independent read-only semantic auditor Poincare returned PASS, including
the regression audit. Separate QA rerun log: `/tmp/signed-radius-qa.log`;
independent QA-A Popper returned ACCEPTED_WITH_LIMITED_SCOPE: locked build
exit 0, strict screening and diff/no-hole checks passed. Acceptance covers
these signed-radius formulas, not the whole repository.

The whole-index proof-proxy gate failed on missing headers in concurrently
edited `Lie/CanonicalZornG2AppendixDSourceBridge.lean` and
`Lie/CanonicalZornStandardDerivationActions.lean`, outside this change.
This is not a claim of a clean repository-wide gate or completed inventory.
