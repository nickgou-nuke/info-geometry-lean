# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:13.657404+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesCommutantGeometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **9**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesCommutantGeometry.lean` | `advisory` | 30 | 0 | 9 | 12 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesCommutantGeometry.lean`
- module: `InfoGeometry.Canonical.HestenesCommutantGeometry`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L113 [soft] `simp-law-injection` in `simp-declaration hestenesLeftCoeff_zero_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `skeletal-proof` in `theorem hestenesLeftCoeff_zero_zero` — proof appears to close via minimal tactic one-liner
  - L118 [soft] `simp-law-injection` in `simp-declaration hestenesLeftCoeff_one_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [soft] `skeletal-proof` in `theorem hestenesLeftCoeff_one_zero` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `simp-law-injection` in `simp-declaration hestenesLeftCoeff_zero_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `skeletal-proof` in `theorem hestenesLeftCoeff_zero_one` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `skeletal-proof` in `theorem hestenesLeftCoeff_mul` — proof appears to close via minimal tactic one-liner
  - L145 [advisory] `local-hypothesis-injection` in `theorem hestenesLeftCoeff_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L146 [advisory] `local-hypothesis-injection` in `theorem hestenesLeftCoeff_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L147 [advisory] `local-hypothesis-injection` in `theorem hestenesLeftCoeff_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L155 [advisory] `local-hypothesis-injection` in `theorem hestenesLeftCoeff_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L160 [advisory] `local-hypothesis-injection` in `theorem hestenesLeftCoeff_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L185 [advisory] `local-hypothesis-injection` in `theorem hestenesLeftCoeff_eq_hestenesCoeff_of_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L205 [soft] `skeletal-proof` in `theorem conjugate_hestenesLeftCoeff_of_preservesK` — proof appears to close via minimal tactic one-liner
  - L213 [advisory] `local-hypothesis-injection` in `theorem conjugate_hestenesLeftCoeff_of_preservesK` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L237 [soft] `skeletal-proof` in `theorem conjugate_hestenesLeftCoeff_of_flipsK` — proof appears to close via minimal tactic one-liner
  - L245 [advisory] `local-hypothesis-injection` in `theorem conjugate_hestenesLeftCoeff_of_flipsK` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

