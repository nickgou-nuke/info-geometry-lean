# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:31.844695+00:00`
Root: `lean/InfoGeometry/Projective/Rays.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **2**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/Rays.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Projective/Rays.lean`
- module: `InfoGeometry.Projective.Rays`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [advisory] `existential-packaging` in `def same_ray` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L72 [advisory] `existential-packaging` in `lemma same_ray_iff_gauge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L83 [soft] `skeletal-proof` in `lemma projectivize_eq_projectivize_smul` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `simp-law-injection` in `simp-declaration projectivize_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

