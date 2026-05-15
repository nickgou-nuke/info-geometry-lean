# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:06.400841+00:00`
Root: `lean/InfoGeometry/Canonical/EPAndGroupInverse.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **9**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/EPAndGroupInverse.lean` | `advisory` | 24 | 0 | 9 | 6 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/EPAndGroupInverse.lean`
- module: `InfoGeometry.Canonical.EPAndGroupInverse`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L53 [soft] `skeletal-proof` in `theorem isEP_of_dilationGap_eq_zero` — proof appears to close via minimal tactic one-liner
  - L58 [advisory] `local-hypothesis-injection` in `theorem isEP_of_dilationGap_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L61 [advisory] `local-hypothesis-injection` in `theorem isEP_of_dilationGap_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L77 [soft] `skeletal-proof` in `theorem moorePenrose_isDrazinInverse_one_of_isEP` — proof appears to close via minimal tactic one-liner
  - L116 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L122 [soft] `skeletal-proof` in `theorem isEP_iff_comm` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `skeletal-proof` in `theorem rightProjectorMismatch_eq_projectorMismatch_of_isEP` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `skeletal-proof` in `theorem dilationGap_eq_zero_of_isEP` — proof appears to close via minimal tactic one-liner
  - L150 [soft] `skeletal-proof` in `theorem isEP_of_dilationGap_eq_zero` — proof appears to close via minimal tactic one-liner
  - L165 [soft] `skeletal-proof` in `theorem rightChiralAnomaly_eq_chiralAnomaly_of_isEP` — proof appears to close via minimal tactic one-liner
  - L178 [advisory] `local-hypothesis-injection` in `theorem spectralProjector_commutator_dilationGap_eq_zero_of_isEP` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L180 [soft] `skeletal-proof` in `theorem moorePenrose_isDrazinInverse_one_of_isEP` — proof appears to close via minimal tactic one-liner
  - L190 [soft] `skeletal-proof` in `theorem moorePenrose_isDrazinInverse_one_of_dilationGap_eq_zero` — proof appears to close via minimal tactic one-liner

