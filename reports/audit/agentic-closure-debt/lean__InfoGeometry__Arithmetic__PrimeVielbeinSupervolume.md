# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:33.027977+00:00`
Root: `lean/InfoGeometry/Arithmetic/PrimeVielbeinSupervolume.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **5**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/PrimeVielbeinSupervolume.lean` | `advisory` | 11 | 0 | 5 | 1 | 6 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/PrimeVielbeinSupervolume.lean`
- module: `InfoGeometry.Arithmetic.PrimeVielbeinSupervolume`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [soft] `skeletal-proof` in `theorem finitePrimeVielbeinSupertrace_eq_supervolume` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `law-field-locker` in `structure-field PrimeVielbeinReadout.supertrace_eq_supervolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [soft] `law-field-locker` in `structure-field PrimeVielbeinGate.supervolume_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `simp-law-injection` in `simp-declaration finitePrimeVielbeinEffectiveAction_eq_neg_log_supervolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [soft] `skeletal-proof` in `theorem finitePrimeVielbeinEffectiveAction_eq_neg_log_supervolume` — proof appears to close via minimal tactic one-liner

