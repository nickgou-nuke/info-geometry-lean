# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:17.852995+00:00`
Root: `lean/InfoGeometry/Clifford/Hestenes.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **2**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/Hestenes.lean` | `advisory` | 9 | 0 | 2 | 5 | 7 |

## Findings by file

### `lean/InfoGeometry/Clifford/Hestenes.lean`
- module: `InfoGeometry.Clifford.Hestenes`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `skeletal-proof` in `theorem pseudoscalar_sq` — proof appears to close via minimal tactic one-liner
  - L40 [advisory] `local-hypothesis-injection` in `theorem pseudoscalar_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L45 [advisory] `local-hypothesis-injection` in `theorem pseudoscalar_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L47 [advisory] `local-hypothesis-injection` in `theorem pseudoscalar_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L78 [advisory] `existential-packaging` in `def IsSignedVolume` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L89 [soft] `skeletal-proof` in `lemma cl11Rep_pseudoscalar_eq_spectral_epsilon` — proof appears to close via minimal tactic one-liner

