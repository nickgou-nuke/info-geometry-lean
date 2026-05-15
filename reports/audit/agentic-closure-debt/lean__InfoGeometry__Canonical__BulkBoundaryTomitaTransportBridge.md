# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:46.861239+00:00`
Root: `lean/InfoGeometry/Canonical/BulkBoundaryTomitaTransportBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **16**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BulkBoundaryTomitaTransportBridge.lean` | `advisory` | 39 | 0 | 16 | 7 | 23 |

## Findings by file

### `lean/InfoGeometry/Canonical/BulkBoundaryTomitaTransportBridge.lean`
- module: `InfoGeometry.Canonical.BulkBoundaryTomitaTransportBridge`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L56 [soft] `law-field-locker` in `structure-field ModularBulkBoundaryBridge.logData` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field ModularBulkBoundaryBridge.delta_agrees` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field ModularBulkBoundaryBridge.majorana` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field ModularBulkBoundaryBridge.localOp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field ModularBulkBoundaryBridge.transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field ModularBulkBoundaryBridge.transport_eq_flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field ModularBulkBoundaryBridge.transport_eq_inverseFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field ModularBulkBoundaryBridge.transport_preserves_chirality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L71 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L76 [soft] `skeletal-proof` in `theorem carrier_modularFlow_eq_logData_generator` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `skeletal-proof` in `theorem owner_hasZeroMode` — proof appears to close via minimal tactic one-liner
  - L114 [advisory] `existential-packaging` in `theorem owner_exists_zeroMode` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L114 [soft] `skeletal-proof` in `theorem owner_exists_zeroMode` — proof appears to close via minimal tactic one-liner
  - L131 [advisory] `existential-packaging` in `theorem transported_exists_zeroMode` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L200 [soft] `skeletal-proof` in `theorem transportedOperator_eq_wedgeBoost_conjugate` — proof appears to close via minimal tactic one-liner
  - L211 [soft] `skeletal-proof` in `theorem transportedOperator_wedge_roundtrip` — proof appears to close via minimal tactic one-liner
  - L221 [soft] `skeletal-proof` in `theorem transportedOperator_eq_wedge_roundtrip_conjugate` — proof appears to close via minimal tactic one-liner
  - L233 [advisory] `existential-packaging` in `theorem transported_weylZeroModePair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L233 [soft] `skeletal-proof` in `theorem transported_weylZeroModePair` — proof appears to close via minimal tactic one-liner

