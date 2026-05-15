# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:52.339780+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralNullSpaceBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **7**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralNullSpaceBridge.lean` | `advisory` | 16 | 0 | 7 | 2 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralNullSpaceBridge.lean`
- module: `InfoGeometry.Canonical.ChiralNullSpaceBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L29 [soft] `law-field-locker` in `structure-field ZeroModeSubtractionWitness.heatKernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field ZeroModeSubtractionWitness.vacuum_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field ZeroModeSubtractionWitness.regulatedHeatKernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field ZeroModeSubtractionWitness.regulated_eq_subtract` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `skeletal-proof` in `theorem drazinCore_eq_kernel` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem excitedStateSector_eq_orthogonal` — proof appears to close via minimal tactic one-liner
  - L51 [soft] `skeletal-proof` in `theorem regulatedHeatKernel_eq_subtract_one` — proof appears to close via minimal tactic one-liner

