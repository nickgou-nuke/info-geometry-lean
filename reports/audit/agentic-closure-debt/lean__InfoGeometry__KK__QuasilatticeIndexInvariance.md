# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:46.946096+00:00`
Root: `lean/InfoGeometry/KK/QuasilatticeIndexInvariance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **1**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/QuasilatticeIndexInvariance.lean` | `advisory` | 13 | 0 | 1 | 11 | 12 |

## Findings by file

### `lean/InfoGeometry/KK/QuasilatticeIndexInvariance.lean`
- module: `InfoGeometry.KK.QuasilatticeIndexInvariance`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L103 [soft] `simp-law-injection` in `simp-declaration quasilatticeDirac_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [advisory] `local-hypothesis-injection` in `def quasilatticeAnalyticalIndex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L128 [advisory] `local-hypothesis-injection` in `def quasilatticeAnalyticalIndex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L130 [advisory] `local-hypothesis-injection` in `def quasilatticeAnalyticalIndex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L150 [advisory] `local-hypothesis-injection` in `def quasilatticeAnalyticalIndex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [advisory] `local-hypothesis-injection` in `def quasilatticeAnalyticalIndex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L197 [advisory] `local-hypothesis-injection` in `def quasilatticeAnalyticalIndex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L349 [advisory] `local-hypothesis-injection` in `def quasilatticeAnalyticalIndex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L357 [advisory] `local-hypothesis-injection` in `def quasilatticeAnalyticalIndex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

