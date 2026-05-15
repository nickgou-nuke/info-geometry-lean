# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:48.502703+00:00`
Root: `lean/InfoGeometry/Canonical/CartanBerezinianCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CartanBerezinianCore.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/CartanBerezinianCore.lean`
- module: `InfoGeometry.Canonical.CartanBerezinianCore`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [soft] `law-field-locker` in `structure-field SchurAdmissibleTransport.T` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L19 [soft] `law-field-locker` in `structure-field SchurAdmissibleTransport.hD` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L21 [soft] `law-field-locker` in `structure-field SchurAdmissibleTransport.hSchur` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `simp-law-injection` in `simp-declaration generalizedBerezinian_eq_restrictedVolumeCharacter` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration generalizedBerezinianScale_eq_restrictedVolumeScale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `skeletal-proof` in `theorem schur_eq_plusBlock_of_offDiagonal_vanish` — proof appears to close via minimal tactic one-liner

