# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:05.235046+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/AndreevBoundary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **13**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/AndreevBoundary.lean` | `advisory` | 33 | 0 | 13 | 7 | 20 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/AndreevBoundary.lean`
- module: `InfoGeometry.OperatorAlgebra.AndreevBoundary`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `simp-law-injection` in `simp-declaration flip_electronLike` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `skeletal-proof` in `theorem flip_electronLike` — proof appears to close via minimal tactic one-liner
  - L51 [soft] `simp-law-injection` in `simp-declaration flip_holeLike` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `skeletal-proof` in `theorem flip_holeLike` — proof appears to close via minimal tactic one-liner
  - L56 [soft] `simp-law-injection` in `simp-declaration flip_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L158 [soft] `law-field-locker` in `structure-field AndreevSwapWitness.theta_electron` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `law-field-locker` in `structure-field AndreevSwapWitness.theta_hole` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L160 [advisory] `bridge-shaped-declaration` in `theorem electron_hole_diagonal_fixed_of_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L196 [soft] `law-field-locker` in `structure-field AndreevBoundaryDatum.theta_electron` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L321 [soft] `law-field-locker` in `structure-field BoundaryClosureWitness.imbalance_anti_fixed_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L329 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L372 [soft] `law-field-locker` in `structure-field AndreevChargeLedger.chargeOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L380 [soft] `law-field-locker` in `structure-field AndreevChargeLedger.charge_balance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L394 [soft] `law-field-locker` in `structure-field ChargeBalanceWitness.certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L404 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L412 [advisory] `bridge-shaped-declaration` in `theorem charge_balance_valid_of_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L426 [advisory] `bridge-shaped-declaration` in `theorem diagonal_fixed_of_boundary_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L426 [soft] `skeletal-proof` in `theorem diagonal_fixed_of_boundary_witness` — proof appears to close via minimal tactic one-liner

