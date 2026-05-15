# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:47.920158+00:00`
Root: `lean/InfoGeometry/Canonical/RealBerryRotorBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **9**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealBerryRotorBridge.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealBerryRotorBridge.lean`
- module: `InfoGeometry.Canonical.RealBerryRotorBridge`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.hsmul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.basisMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.spinExp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.hstab_i` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.hstab_rho` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.regularizedStokesLimit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `skeletal-proof` in `theorem realModularBerryRotorBridge_tendsto` — proof appears to close via minimal tactic one-liner
  - L204 [soft] `law-field-locker` in `structure-field SplitRealBerryRotorShadow.supervolumePotential_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `simp-law-injection` in `simp-declaration supervolumePotential_eq_supertraceReadout` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

