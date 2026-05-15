# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:51.597487+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralHodgeCartanBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralHodgeCartanBridge.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralHodgeCartanBridge.lean`
- module: `InfoGeometry.Canonical.ChiralHodgeCartanBridge`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L115 [soft] `skeletal-proof` in `theorem theta_involutive` — proof appears to close via minimal tactic one-liner
  - L132 [soft] `skeletal-proof` in `theorem theta_alias_eq_thetaGamma` — proof appears to close via minimal tactic one-liner
  - L140 [soft] `skeletal-proof` in `theorem thetaPhase_involutive` — proof appears to close via minimal tactic one-liner
  - L157 [soft] `skeletal-proof` in `theorem cartanOdd_of_anticommutes_gamma` — proof appears to close via minimal tactic one-liner
  - L177 [soft] `skeletal-proof` in `theorem dirac_square_commutes_gamma` — proof appears to close via minimal tactic one-liner
  - L218 [soft] `skeletal-proof` in `theorem phaseCartanOdd_of_anticommutes` — proof appears to close via minimal tactic one-liner
  - L239 [soft] `skeletal-proof` in `theorem phaseCartanEven_of_commutes` — proof appears to close via minimal tactic one-liner

