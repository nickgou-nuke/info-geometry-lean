# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:39.064423+00:00`
Root: `lean/InfoGeometry/Singular/CartanWiring.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **6**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Singular/CartanWiring.lean` | `advisory` | 15 | 0 | 6 | 3 | 9 |

## Findings by file

### `lean/InfoGeometry/Singular/CartanWiring.lean`
- module: `InfoGeometry.Singular.CartanWiring`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [soft] `simp-law-injection` in `simp-declaration CartanAdjoint_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L23 [soft] `simp-law-injection` in `simp-declaration CartanAdjoint_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L29 [soft] `simp-law-injection` in `simp-declaration CartanAdjoint_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `simp-law-injection` in `simp-declaration CartanAdjoint_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration CartanAdjoint_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `simp-law-injection` in `simp-declaration CartanAdjoint_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [advisory] `local-hypothesis-injection` in `def CartanAdjoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L54 [advisory] `local-hypothesis-injection` in `def CartanAdjoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

