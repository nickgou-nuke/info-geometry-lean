# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:43.998234+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **16**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean` | `advisory` | 35 | 0 | 16 | 3 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean`
- module: `InfoGeometry.Canonical.BogoliubovProjectorTransport`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [soft] `skeletal-proof` in `theorem spectral_epsilon_comp_spectralPlusProj` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `skeletal-proof` in `theorem spectral_epsilon_comp_spectralMinusProj` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem spectralPlusProj_comp_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `theorem spectralMinusProj_comp_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `skeletal-proof` in `theorem spectralPlusProj_comp_modular_j` — proof appears to close via minimal tactic one-liner
  - L114 [soft] `skeletal-proof` in `theorem spectralMinusProj_comp_modular_j` — proof appears to close via minimal tactic one-liner
  - L131 [soft] `skeletal-proof` in `theorem spectralPlusProj_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `skeletal-proof` in `theorem spectralMinusProj_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L153 [soft] `skeletal-proof` in `theorem spectralPlusProj_comp_epsilonBoost` — proof appears to close via minimal tactic one-liner
  - L169 [soft] `skeletal-proof` in `theorem spectralMinusProj_comp_epsilonBoost` — proof appears to close via minimal tactic one-liner
  - L272 [soft] `skeletal-proof` in `theorem modular_j_maps_plusSheet_to_minusSheet` — proof appears to close via minimal tactic one-liner
  - L287 [soft] `skeletal-proof` in `theorem modular_j_maps_minusSheet_to_plusSheet` — proof appears to close via minimal tactic one-liner
  - L302 [soft] `skeletal-proof` in `theorem complex_i_maps_plusSheet_to_minusSheet` — proof appears to close via minimal tactic one-liner
  - L317 [soft] `skeletal-proof` in `theorem complex_i_maps_minusSheet_to_plusSheet` — proof appears to close via minimal tactic one-liner
  - L324 [soft] `skeletal-proof` in `theorem modularTransportFlow_deriv` — proof appears to close via minimal tactic one-liner
  - L337 [soft] `skeletal-proof` in `theorem spectralPlusProj_commutes_modularTransportFlow` — proof appears to close via minimal tactic one-liner

