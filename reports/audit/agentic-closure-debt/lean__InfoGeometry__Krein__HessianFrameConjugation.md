# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:51.145917+00:00`
Root: `lean/InfoGeometry/Krein/HessianFrameConjugation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **8**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HessianFrameConjugation.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/Krein/HessianFrameConjugation.lean`
- module: `InfoGeometry.Krein.HessianFrameConjugation`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `simp-law-injection` in `simp-declaration hessianFrameConjugation_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L42 [soft] `simp-law-injection` in `simp-declaration hessianFrameConjugation_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration hessianFrameConjugation_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration hessianFrameConjugation_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration hessianFrameConjugation_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `theorem hessianFrameConjugation_modularJ_involutive` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `skeletal-proof` in `theorem hessianFrameConjugation_modularJ_comp` — proof appears to close via minimal tactic one-liner
  - L110 [soft] `skeletal-proof` in `theorem hessianFrameConjugation_modularJ_lie` — proof appears to close via minimal tactic one-liner

