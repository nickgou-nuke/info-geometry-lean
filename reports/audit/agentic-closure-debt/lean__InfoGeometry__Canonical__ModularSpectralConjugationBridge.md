# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:30.080306+00:00`
Root: `lean/InfoGeometry/Canonical/ModularSpectralConjugationBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **4**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularSpectralConjugationBridge.lean` | `advisory` | 15 | 0 | 4 | 7 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularSpectralConjugationBridge.lean`
- module: `InfoGeometry.Canonical.ModularSpectralConjugationBridge`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L50 [soft] `skeletal-proof` in `theorem activeModularConjugation_eq_modular_j_mul_active` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `skeletal-proof` in `theorem activeModularConjugation_mul_P_D_eq_zero` — proof appears to close via minimal tactic one-liner
  - L82 [advisory] `local-hypothesis-injection` in `theorem activeModularConjugation_mul_P_D_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L84 [advisory] `local-hypothesis-injection` in `theorem activeModularConjugation_mul_P_D_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L102 [soft] `skeletal-proof` in `theorem P_D_mul_activeModularConjugation_eq_zero` — proof appears to close via minimal tactic one-liner
  - L113 [advisory] `local-hypothesis-injection` in `theorem P_D_mul_activeModularConjugation_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L115 [advisory] `local-hypothesis-injection` in `theorem P_D_mul_activeModularConjugation_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L139 [soft] `skeletal-proof` in `theorem activeModularConjugation_eq_modular_j_mul_spectralProjector` — proof appears to close via minimal tactic one-liner

