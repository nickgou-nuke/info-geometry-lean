# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:34.331147+00:00`
Root: `lean/InfoGeometry/Canonical/OnsagerCasimirJ.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **7**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OnsagerCasimirJ.lean` | `advisory` | 20 | 0 | 7 | 6 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/OnsagerCasimirJ.lean`
- module: `InfoGeometry.Canonical.OnsagerCasimirJ`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [soft] `skeletal-proof` in `theorem modularComplexI_comp_modularConjugationJ` — proof appears to close via minimal tactic one-liner
  - L51 [advisory] `local-hypothesis-injection` in `theorem modularComplexI_comp_modularConjugationJ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L64 [soft] `skeletal-proof` in `theorem complex_i_comp_modularConjugationJ` — proof appears to close via minimal tactic one-liner
  - L78 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L80 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L106 [soft] `simp-law-injection` in `simp-declaration JConjugate_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L111 [soft] `simp-law-injection` in `simp-declaration JConjugate_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [advisory] `local-hypothesis-injection` in `def IsJOdd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [soft] `skeletal-proof` in `theorem JConjugate_channelPhaseAxis_eq_neg_channelPhaseAxis_JConjugate` — proof appears to close via minimal tactic one-liner
  - L158 [soft] `skeletal-proof` in `theorem twoStateObservableCorrelation_J_conjugate` — proof appears to close via minimal tactic one-liner
  - L235 [soft] `skeletal-proof` in `theorem stateRelativeModularGenerator_right_eq_JConjugate_left` — proof appears to close via minimal tactic one-liner

