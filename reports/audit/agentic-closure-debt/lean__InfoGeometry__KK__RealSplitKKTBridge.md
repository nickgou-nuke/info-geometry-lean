# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:47.066495+00:00`
Root: `lean/InfoGeometry/KK/RealSplitKKTBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **1**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/RealSplitKKTBridge.lean` | `advisory` | 8 | 0 | 1 | 6 | 7 |

## Findings by file

### `lean/InfoGeometry/KK/RealSplitKKTBridge.lean`
- module: `InfoGeometry.KK.RealSplitKKTBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L41 [soft] `law-field-locker` in `structure-field GradeEpsWitness.grade_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [advisory] `local-hypothesis-injection` in `structure GradeEpsWitness` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L60 [advisory] `local-hypothesis-injection` in `structure GradeEpsWitness` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L70 [advisory] `local-hypothesis-injection` in `structure GradeEpsWitness` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L80 [advisory] `local-hypothesis-injection` in `structure GradeEpsWitness` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

