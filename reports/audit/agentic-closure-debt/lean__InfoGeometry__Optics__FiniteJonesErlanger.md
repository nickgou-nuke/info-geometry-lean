# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:27.309316+00:00`
Root: `lean/InfoGeometry/Optics/FiniteJonesErlanger.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **5**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Optics/FiniteJonesErlanger.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Optics/FiniteJonesErlanger.lean`
- module: `InfoGeometry.Optics.FiniteJonesErlanger`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field InvertibleTransport.val_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field InvertibleTransport.inv_val` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `skeletal-proof` in `theorem conjugate_fixed_of_commute` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `skeletal-proof` in `theorem conjugate_preserves_idempotent` — proof appears to close via minimal tactic one-liner
  - L195 [soft] `skeletal-proof` in `theorem brewsterMatrix_invariant_under_diagonalJonesTransport` — proof appears to close via minimal tactic one-liner
  - L208 [advisory] `local-hypothesis-injection` in `theorem brewsterMatrix_invariant_under_diagonalJonesTransport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

