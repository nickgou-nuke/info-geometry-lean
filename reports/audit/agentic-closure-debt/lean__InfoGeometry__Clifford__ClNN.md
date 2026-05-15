# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:16.905204+00:00`
Root: `lean/InfoGeometry/Clifford/ClNN.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **12**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/ClNN.lean` | `advisory` | 27 | 0 | 12 | 3 | 15 |

## Findings by file

### `lean/InfoGeometry/Clifford/ClNN.lean`
- module: `InfoGeometry.Clifford.ClNN`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L62 [soft] `simp-law-injection` in `simp-declaration quad_headPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration quad_tailLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration polar_headPair_tailLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [advisory] `local-hypothesis-injection` in `def headNullPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [soft] `simp-law-injection` in `simp-declaration headNullMinus_isotropic` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L92 [soft] `simp-law-injection` in `simp-declaration headNullPlus_isotropic` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [soft] `simp-law-injection` in `simp-declaration polar_headNullMinus_headNullPlus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [advisory] `local-hypothesis-injection` in `def headNullPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L122 [soft] `simp-law-injection` in `simp-declaration gammaHeadNullMinus_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L128 [soft] `simp-law-injection` in `simp-declaration gammaHeadNullPlus_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L134 [soft] `simp-law-injection` in `simp-declaration gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L143 [soft] `simp-law-injection` in `simp-declaration gammaHeadNullPlus_mul_gammaHeadNullMinus_add_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L149 [soft] `simp-law-injection` in `simp-declaration gammaHeadNullMinus_mul_gammaTail_add_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L157 [soft] `simp-law-injection` in `simp-declaration gammaHeadNullPlus_mul_gammaTail_add_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

