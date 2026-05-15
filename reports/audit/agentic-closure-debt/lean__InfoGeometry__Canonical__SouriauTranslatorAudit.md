# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:59.129403+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauTranslatorAudit.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **1**
- Advisory: **18**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauTranslatorAudit.lean` | `advisory` | 20 | 0 | 1 | 18 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauTranslatorAudit.lean`
- module: `InfoGeometry.Canonical.SouriauTranslatorAudit`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L64 [soft] `skeletal-proof` in `theorem alignedWithSouriauTranslator_eq_expected` — proof appears to close via minimal tactic one-liner
  - L77 [advisory] `existential-packaging` in `theorem audit_claimA_massieu_eq_log_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L87 [advisory] `existential-packaging` in `theorem audit_claimB_firstDerivatives_eq_moments` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L100 [advisory] `existential-packaging` in `theorem audit_claimC_hessian_eq_fisher_eq_covariance` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L121 [advisory] `bridge-shaped-declaration` in `theorem audit_claimD_fenchelLegendre_contact_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L121 [advisory] `existential-packaging` in `theorem audit_claimD_fenchelLegendre_contact_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L135 [advisory] `existential-packaging` in `theorem audit_claimE_entropyProduction_nonneg_of_PSD` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L148 [advisory] `existential-packaging` in `theorem audit_claimE_entropyProduction_nonneg_of_det_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L163 [advisory] `existential-packaging` in `theorem audit_claimE_entropyProduction_eq_zero_iff_force_zero_of_PD` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L181 [advisory] `existential-packaging` in `theorem audit_finite_inverseFisherMetric_of_det_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L221 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L223 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L230 [advisory] `bridge-shaped-declaration` in `theorem audit_claimD_operatorLegendre_inverseHessian_eq_inverseFisher_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L253 [advisory] `existential-packaging` in `theorem audit_analyticEnrichmentTranslatorPacket` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L271 [advisory] `bridge-shaped-declaration` in `theorem audit_claimCD_fullCoadjointOrbit_hessian_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L295 [advisory] `bridge-shaped-declaration` in `theorem audit_claimCD_fullCoadjointOrbit_strict_hessian_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L320 [advisory] `bridge-shaped-declaration` in `theorem audit_claimCDE_fullCoadjointOrbit_hessian_metriplectic_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L347 [advisory] `bridge-shaped-declaration` in `theorem audit_claimCDE_fullCoadjointOrbit_strict_hessian_metriplectic_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

