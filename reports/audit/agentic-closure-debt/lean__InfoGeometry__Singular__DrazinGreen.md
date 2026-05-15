# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:39.454715+00:00`
Root: `lean/InfoGeometry/Singular/DrazinGreen.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **5**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Singular/DrazinGreen.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Singular/DrazinGreen.lean`
- module: `InfoGeometry.Singular.DrazinGreen`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `skeletal-proof` in `theorem A_mul_Drazin_Green_eq_projector` — proof appears to close via minimal tactic one-liner
  - L55 [soft] `skeletal-proof` in `theorem Drazin_Projector_mul_Green_eq_Green` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `skeletal-proof` in `theorem Green_mul_Drazin_Projector_eq_Green` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `skeletal-proof` in `theorem Drazin_Projector_mul_A_eq_A_mul_Drazin_Projector` — proof appears to close via minimal tactic one-liner
  - L95 [advisory] `local-hypothesis-injection` in `theorem Drazin_ResidueProjector_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L135 [soft] `skeletal-proof` in `theorem A_mul_drazinGreen_eq_drazinProjector` — proof appears to close via minimal tactic one-liner

