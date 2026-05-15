# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:28.724052+00:00`
Root: `lean/InfoGeometry/Potential/Thermo.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **13**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Potential/Thermo.lean` | `advisory` | 27 | 0 | 13 | 1 | 14 |

## Findings by file

### `lean/InfoGeometry/Potential/Thermo.lean`
- module: `InfoGeometry.Potential.Thermo`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field LegendreModel.grad` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field LegendreModel.fenchel_ineq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field LegendreModel.contact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `simp-law-injection` in `simp-declaration massieu_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration partition_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration dualCoord_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L73 [soft] `simp-law-injection` in `simp-declaration fenchelGap_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [soft] `skeletal-proof` in `lemma contact_balance` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `simp-law-injection` in `simp-declaration freeEnergy_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [soft] `simp-law-injection` in `simp-declaration canonicalEnergy_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L127 [soft] `simp-law-injection` in `simp-declaration canonicalEntropy_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration canonicalFreeEnergy_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L135 [soft] `simp-law-injection` in `simp-declaration scaledFenchelGap_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

