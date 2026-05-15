# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:04.705601+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **12**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean` | `advisory` | 36 | 0 | 12 | 12 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L84 [soft] `skeletal-proof` in `theorem GammaS_eq_two_mul_P_D_sub_one` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `skeletal-proof` in `theorem GammaS_mul_P_D` — proof appears to close via minimal tactic one-liner
  - L100 [advisory] `local-hypothesis-injection` in `theorem P_D_mul_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [soft] `skeletal-proof` in `theorem GammaS_mul_Q_D` — proof appears to close via minimal tactic one-liner
  - L116 [advisory] `local-hypothesis-injection` in `theorem Q_D_mul_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L122 [soft] `skeletal-proof` in `theorem commutator_P_D_GammaG_eq_rightSupercharge_sub_leftSupercharge` — proof appears to close via minimal tactic one-liner
  - L132 [soft] `skeletal-proof` in `theorem commutator_P_D_G_eq_half_sub_supercharges` — proof appears to close via minimal tactic one-liner
  - L144 [soft] `skeletal-proof` in `theorem anticommutator_GammaS_leftSupercharge_eq_zero` — proof appears to close via minimal tactic one-liner
  - L148 [advisory] `local-hypothesis-injection` in `theorem anticommutator_GammaS_leftSupercharge_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L158 [soft] `skeletal-proof` in `theorem anticommutator_GammaS_rightSupercharge_eq_zero` — proof appears to close via minimal tactic one-liner
  - L162 [advisory] `local-hypothesis-injection` in `theorem anticommutator_GammaS_rightSupercharge_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L172 [soft] `skeletal-proof` in `theorem leftSupercharge_isSpectralNonCompact` — proof appears to close via minimal tactic one-liner
  - L179 [soft] `skeletal-proof` in `theorem rightSupercharge_isSpectralNonCompact` — proof appears to close via minimal tactic one-liner
  - L191 [advisory] `existential-packaging` in `def IsInRegularSector` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L196 [advisory] `existential-packaging` in `def IsInNullSector` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L221 [soft] `skeletal-proof` in `theorem maps_regular_sector_of_preservesP_D` — proof appears to close via minimal tactic one-liner
  - L227 [advisory] `local-hypothesis-injection` in `theorem maps_regular_sector_of_preservesP_D` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L235 [soft] `skeletal-proof` in `theorem maps_null_sector_of_preservesQ_D` — proof appears to close via minimal tactic one-liner
  - L241 [advisory] `local-hypothesis-injection` in `theorem maps_null_sector_of_preservesQ_D` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L280 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L296 [soft] `skeletal-proof` in `theorem centralSupercharge_transport_invariant` — proof appears to close via minimal tactic one-liner

