# Debt Candidates

This note is a report-only constructive replacement queue derived from the tracked
surrogate, vacuity, and thin-bridge audits.

It is not a proof artifact.

The purpose is to pin exact debt targets that can be attacked by a creative lane,
shrunk by a critical lane, and then materialized into quarantine for Lean validation.

## Audit Context

- surrogate findings: `1`
- vacuity findings: `0`
- thin-bridge findings: `1`
- aggregated replacement targets: `2`

## Selection Rule

- Prefer canonical/stable declarations over unstable/archive surfaces.
- Prefer critical/high findings over medium/low findings.
- Aggregate duplicate targets when multiple audits point at the same declaration.
- Keep every candidate tied to a real file:line surface already tracked by the audits.

## Candidate 1

`name`

`DebtCandidate.repair_expressing_1`

`Lean-style signature sketch`

```lean
axiom expressing the modular symmetry relation at the carrier level.
-/ := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `expressing` at `lean/InfoGeometry/Quantum/ModularAnomaly.lean:261`. It aggregates the audit signals `surrogate:axiom_decl (critical)`. A successful replacement would replace the explicit axiom with a proved theorem surface.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Quantum/ModularAnomaly.lean`
- `target line: 261`
- `strongest priority: critical`
- `audit signals: surrogate:axiom_decl (critical)`
- `nearby declarations: einstein_anomaly_is_modular_generator, IdCLM, expFlow, expFlow_toContinuousLinearMap, expFlow_zero, expFlow_add`
- `surrogate debt goal: replace the explicit axiom with a proved theorem surface`

`risk level`

`high`

## Candidate 2

`name`

`DebtCandidate.repair_unified_anomaly_bridge_2`

`Lean-style signature sketch`

```lean
theorem unified_anomaly_bridge
    (hFlow : HasDerivAt (fun t => (M.sigma t : X →L[ℝ] X)) σGen 0)
    (hFlowNeg : HasDerivAt (fun t => (M.sigma (-t) : X →L[ℝ] X)) (-σGen) 0) :
    M.modularAnomalyGenerator U =
      (U.symm : X →L[ℝ] X).comp
        (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen) := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `unified_anomaly_bridge` at `lean/InfoGeometry/Quantum/ModularAnomaly.lean:131`. It aggregates the audit signals `thinness:direct_forwarder (medium)`. A successful replacement would replace the direct forwarder with a local constructive derivation.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Quantum/ModularAnomaly.lean`
- `target line: 131`
- `strongest priority: medium`
- `audit signals: thinness:direct_forwarder (medium)`
- `nearby declarations: TopologicalMajoranaShadow, modularCocycle, IsAnomalyFree, modularAnomalyGenerator, sigma_zero_clm, modularCocycle_zero`
- `thin-bridge debt goal: replace the direct forwarder with a local constructive derivation`

`risk level`

`medium`
