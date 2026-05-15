# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:29.966168+00:00`
Root: `lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **29**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean` | `advisory` | 59 | 0 | 29 | 1 | 30 |

## Findings by file

### `lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean`
- module: `InfoGeometry.Algebraic.SplitSuperGeometry`
- status: `advisory`
- debt_score: `59`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field ParityInvolution.parity_eq_on_even` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field ParityInvolution.parity_eq_on_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `simp-law-injection` in `simp-declaration parity_parity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration parity_even` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration parity_odd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L93 [soft] `simp-law-injection` in `simp-declaration supertrace_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `skeletal-proof` in `theorem supertrace_zero` — proof appears to close via minimal tactic one-liner
  - L118 [soft] `simp-law-injection` in `simp-declaration cliffordParity_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `simp-law-injection` in `simp-declaration cliffordParity_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration cliffordParity_comp_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L163 [soft] `simp-law-injection` in `simp-declaration splitCliffordParityInvolution_vector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L165 [soft] `skeletal-proof` in `theorem splitCliffordParityInvolution_vector` — proof appears to close via minimal tactic one-liner
  - L201 [soft] `simp-law-injection` in `simp-declaration canonical_parity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L203 [soft] `skeletal-proof` in `theorem canonical_parity` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `law-field-locker` in `structure-field SuperBerezinianReadout.ber` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field SuperBerezinianReadout.ber_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L226 [soft] `law-field-locker` in `structure-field SuperBerezinianReadout.ber_mul_of_parityPreserving` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L257 [soft] `simp-law-injection` in `simp-declaration negLogBer_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L259 [soft] `skeletal-proof` in `theorem negLogBer_one` — proof appears to close via minimal tactic one-liner
  - L294 [soft] `law-field-locker` in `structure-field ParityPreservingOperatorAction.op` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [soft] `law-field-locker` in `structure-field ParityPreservingOperatorAction.commute_parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L337 [soft] `simp-law-injection` in `simp-declaration parityOp_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L344 [soft] `simp-law-injection` in `simp-declaration parityOp_comp_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L346 [soft] `skeletal-proof` in `theorem parityOp_comp_self` — proof appears to close via minimal tactic one-liner
  - L366 [soft] `simp-law-injection` in `simp-declaration superVolumeAnomaly_eq_superBerezinian` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L368 [soft] `skeletal-proof` in `theorem superVolumeAnomaly_eq_superBerezinian` — proof appears to close via minimal tactic one-liner
  - L372 [soft] `simp-law-injection` in `simp-declaration superEffectiveAction_eq_neg_log_superBerezinian` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L374 [soft] `skeletal-proof` in `theorem superEffectiveAction_eq_neg_log_superBerezinian` — proof appears to close via minimal tactic one-liner
  - L378 [soft] `simp-law-injection` in `simp-declaration superBerezinian_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

