# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:23.115404+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SplitCliffordZ2Four.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **17**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SplitCliffordZ2Four.lean` | `advisory` | 36 | 0 | 17 | 2 | 19 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SplitCliffordZ2Four.lean`
- module: `InfoGeometry.OperatorAlgebra.SplitCliffordZ2Four`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `simp-law-injection` in `simp-declaration flipBit_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L31 [soft] `skeletal-proof` in `theorem flipBit_self` — proof appears to close via minimal tactic one-liner
  - L36 [soft] `simp-law-injection` in `simp-declaration flipBit_ne` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [soft] `skeletal-proof` in `theorem flipBit_ne` — proof appears to close via minimal tactic one-liner
  - L44 [soft] `simp-law-injection` in `simp-declaration flipBit_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `theorem chargeSign_flip_ne` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `law-field-locker` in `structure-field FourCartanInvolutions.Hcartan` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field FourCartanInvolutions.involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field FourCartanInvolutions.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field CliffordBitFlip.G` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L125 [soft] `law-field-locker` in `structure-field CliffordBitFlip.anticomm_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L129 [soft] `law-field-locker` in `structure-field CliffordBitFlip.commute_ne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [soft] `skeletal-proof` in `theorem maps_charge_to_flipBit` — proof appears to close via minimal tactic one-liner
  - L191 [soft] `law-field-locker` in `structure-field SplitCliffordAtom.e_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L195 [soft] `law-field-locker` in `structure-field SplitCliffordAtom.f_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [soft] `law-field-locker` in `structure-field SplitCliffordAtom.anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L212 [soft] `skeletal-proof` in `theorem h_sq` — proof appears to close via minimal tactic one-liner

