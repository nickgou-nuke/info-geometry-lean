# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:13.139152+00:00`
Root: `lean/InfoGeometry/Canonical/HeadTrialityCore.lean`
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
| `lean/InfoGeometry/Canonical/HeadTrialityCore.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/HeadTrialityCore.lean`
- module: `InfoGeometry.Canonical.HeadTrialityCore`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L114 [soft] `law-field-locker` in `structure-field MajoranaWeylCoupling.massMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L149 [soft] `simp-law-injection` in `simp-declaration headHyperbolicBoostRotor_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L151 [soft] `skeletal-proof` in `theorem headHyperbolicBoostRotor_zero` — proof appears to close via minimal tactic one-liner

