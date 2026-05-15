# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:18.383789+00:00`
Root: `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`
- module: `InfoGeometry.Clifford.NeutralPhaseSpaceCore`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `simp-law-injection` in `simp-declaration canonicalNeutralBilin_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `simp-law-injection` in `simp-declaration canonicalNeutralForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration canonicalNeutralFormUnscaled_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `simp-law-injection` in `simp-declaration canonicalNeutralForm_fst_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `simp-law-injection` in `simp-declaration canonicalNeutralForm_snd_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [soft] `simp-law-injection` in `simp-declaration canonicalNeutralFormUnscaled_fst_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [soft] `simp-law-injection` in `simp-declaration canonicalNeutralFormUnscaled_snd_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

