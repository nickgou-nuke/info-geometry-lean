# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:33.687612+00:00`
Root: `lean/InfoGeometry/Quantum/CommutingInvolutionCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **3**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/CommutingInvolutionCore.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Quantum/CommutingInvolutionCore.lean`
- module: `InfoGeometry.Quantum.CommutingInvolutionCore`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `simp-law-injection` in `simp-declaration je_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L35 [soft] `simp-law-injection` in `simp-declaration je_comm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L39 [soft] `simp-law-injection` in `simp-declaration je_comm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

