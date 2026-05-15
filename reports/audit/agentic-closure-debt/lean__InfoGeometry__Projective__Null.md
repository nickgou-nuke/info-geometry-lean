# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:31.230377+00:00`
Root: `lean/InfoGeometry/Projective/Null.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **10**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/Null.lean` | `advisory` | 21 | 0 | 10 | 1 | 11 |

## Findings by file

### `lean/InfoGeometry/Projective/Null.lean`
- module: `InfoGeometry.Projective.Null`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L58 [soft] `definitional-equality-bypass` in `cast <cast>` — cast/propext/unsafe equality transport detected; verify this is not hiding a failed `rfl` or definitional-equality hallucination
  - L67 [soft] `definitional-equality-bypass` in `cast <cast>` — cast/propext/unsafe equality transport detected; verify this is not hiding a failed `rfl` or definitional-equality hallucination
  - L68 [soft] `simp-law-injection` in `simp-declaration IsGradePlusRay_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration IsGradeMinusRay_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `skeletal-proof` in `lemma IsGradePlusRay_vacuum` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `skeletal-proof` in `lemma IsGradeMinusRay_vacuum` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `skeletal-proof` in `lemma isMetricNull_smul` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `definitional-equality-bypass` in `cast <cast>` — cast/propext/unsafe equality transport detected; verify this is not hiding a failed `rfl` or definitional-equality hallucination
  - L127 [soft] `simp-law-injection` in `simp-declaration IsMetricNullRay_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `skeletal-proof` in `lemma IsMetricNullRay_vacuum` — proof appears to close via minimal tactic one-liner

