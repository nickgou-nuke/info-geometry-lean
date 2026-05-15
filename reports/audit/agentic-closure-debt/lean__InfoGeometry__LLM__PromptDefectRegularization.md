# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:57.140954+00:00`
Root: `lean/InfoGeometry/LLM/PromptDefectRegularization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **0**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/PromptDefectRegularization.lean` | `advisory` | 8 | 0 | 0 | 8 | 8 |

## Findings by file

### `lean/InfoGeometry/LLM/PromptDefectRegularization.lean`
- module: `InfoGeometry.LLM.PromptDefectRegularization`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L16 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L66 [advisory] `local-hypothesis-injection` in `theorem regularizedCoreUpdate_lambda_invariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L67 [advisory] `local-hypothesis-injection` in `theorem regularizedCoreUpdate_lambda_invariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L72 [advisory] `local-hypothesis-injection` in `theorem regularizedCoreUpdate_lambda_invariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L86 [advisory] `local-hypothesis-injection` in `theorem regularizedCoreUpdate_eq_coreUpdate` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [advisory] `local-hypothesis-injection` in `theorem regularizedCoreUpdate_eq_coreUpdate` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

