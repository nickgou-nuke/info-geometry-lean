# Debt Candidates

This note is a report-only constructive replacement queue derived from the tracked
surrogate, vacuity, and thin-bridge audits.

It is not a proof artifact.

The purpose is to pin exact debt targets that can be attacked by a creative lane,
shrunk by a critical lane, and then materialized into quarantine for Lean validation.

## Audit Context

- surrogate findings: `0`
- vacuity findings: `0`
- thin-bridge findings: `1`
- aggregated replacement targets: `1`

## Selection Rule

- Prefer canonical/stable declarations over unstable/archive surfaces.
- Prefer critical/high findings over medium/low findings.
- Aggregate duplicate targets when multiple audits point at the same declaration.
- Keep every candidate tied to a real file:line surface already tracked by the audits.

## Candidate 1

`name`

`DebtCandidate.repair_rn_potential_eq_neg_log_density_1`

`Lean-style signature sketch`

```lean
theorem rn_potential_eq_neg_log_density (p : FinProb α) (x : α) :
    log_density p x = Real.log (p x).toReal := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `rn_potential_eq_neg_log_density` at `lean/InfoGeometry/Canonical/LogSpineBridge.lean:32`. It aggregates the audit signals `thinness:definitional_identity (high)`. A successful replacement would replace the definitional identity with a substantive proof.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Canonical/LogSpineBridge.lean`
- `target line: 32`
- `strongest priority: high`
- `audit signals: thinness:definitional_identity (high)`
- `nearby declarations: jordan_logdet_eq_zeta_determinant, modular_hamiltonian_to_log_partition, kahler_spine_entropy_identity, freeEnergySpine`
- `thin-bridge debt goal: replace the definitional identity with a substantive proof`

`risk level`

`high`
