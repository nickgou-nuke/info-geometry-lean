# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:30.315212+00:00`
Root: `lean/InfoGeometry/Projective/Dynamics.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **14**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/Dynamics.lean` | `advisory` | 29 | 0 | 14 | 1 | 15 |

## Findings by file

### `lean/InfoGeometry/Projective/Dynamics.lean`
- module: `InfoGeometry.Projective.Dynamics`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `simp-law-injection` in `simp-declaration J_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L39 [soft] `simp-law-injection` in `simp-declaration epsilon_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L43 [soft] `simp-law-injection` in `simp-declaration I_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `skeletal-proof` in `lemma J_comp_epsilon` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `skeletal-proof` in `lemma epsilon_comp_J` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `lemma J_comp_I` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `skeletal-proof` in `lemma I_comp_J` — proof appears to close via minimal tactic one-liner
  - L122 [soft] `skeletal-proof` in `lemma I_comp_epsilon` — proof appears to close via minimal tactic one-liner
  - L136 [soft] `skeletal-proof` in `lemma epsilon_comp_I` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `skeletal-proof` in `lemma J_sq` — proof appears to close via minimal tactic one-liner
  - L185 [soft] `skeletal-proof` in `lemma epsilon_sq` — proof appears to close via minimal tactic one-liner
  - L213 [soft] `simp-law-injection` in `simp-declaration J_vacuum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L216 [soft] `simp-law-injection` in `simp-declaration epsilon_vacuum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L219 [soft] `simp-law-injection` in `simp-declaration I_vacuum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

