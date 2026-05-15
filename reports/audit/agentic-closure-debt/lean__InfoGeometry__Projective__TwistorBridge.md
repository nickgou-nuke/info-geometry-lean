# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:32.093080+00:00`
Root: `lean/InfoGeometry/Projective/TwistorBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **1**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/TwistorBridge.lean` | `advisory` | 4 | 0 | 1 | 2 | 3 |

## Findings by file

### `lean/InfoGeometry/Projective/TwistorBridge.lean`
- module: `InfoGeometry.Projective.TwistorBridge`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L63 [advisory] `local-hypothesis-injection` in `def projectiveClassToTwistor` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L78 [soft] `simp-law-injection` in `simp-declaration projectiveClassToTwistor_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

