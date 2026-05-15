# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:53.864699+00:00`
Root: `lean/InfoGeometry/Krein/PolarizedSector.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **5**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/PolarizedSector.lean` | `advisory` | 16 | 0 | 5 | 6 | 11 |

## Findings by file

### `lean/InfoGeometry/Krein/PolarizedSector.lean`
- module: `InfoGeometry.Krein.PolarizedSector`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L12 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L14 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [soft] `simp-law-injection` in `simp-declaration spectralPlusProj_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L33 [soft] `simp-law-injection` in `simp-declaration spectralMinusProj_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L42 [advisory] `local-hypothesis-injection` in `theorem spectralPlusProj_apply_eq_plusPoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L51 [advisory] `local-hypothesis-injection` in `theorem spectralMinusProj_apply_eq_minusPoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [soft] `skeletal-proof` in `theorem spectralPlusProj_apply_idempotent` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `skeletal-proof` in `theorem spectralMinusProj_apply_idempotent` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `skeletal-proof` in `theorem spectralProj_decomposition` — proof appears to close via minimal tactic one-liner

