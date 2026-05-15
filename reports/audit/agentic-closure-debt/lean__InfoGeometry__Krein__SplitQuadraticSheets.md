# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:54.638815+00:00`
Root: `lean/InfoGeometry/Krein/SplitQuadraticSheets.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **8**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/SplitQuadraticSheets.lean` | `advisory` | 23 | 0 | 8 | 7 | 15 |

## Findings by file

### `lean/InfoGeometry/Krein/SplitQuadraticSheets.lean`
- module: `InfoGeometry.Krein.SplitQuadraticSheets`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L9 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L29 [soft] `simp-law-injection` in `simp-declaration fst_plusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `simp-law-injection` in `simp-declaration snd_plusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L39 [soft] `simp-law-injection` in `simp-declaration fst_minusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `simp-law-injection` in `simp-declaration snd_minusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration plusPoint_mem_plusSheet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `simp-law-injection` in `simp-declaration minusPoint_mem_minusSheet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `simp-law-injection` in `simp-declaration mem_plusSheet_iff_snd_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [advisory] `local-hypothesis-injection` in `def minusPoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L67 [advisory] `local-hypothesis-injection` in `def minusPoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L70 [advisory] `local-hypothesis-injection` in `def minusPoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L78 [soft] `simp-law-injection` in `simp-declaration mem_minusSheet_iff_fst_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [advisory] `local-hypothesis-injection` in `def minusPoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L85 [advisory] `local-hypothesis-injection` in `def minusPoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

