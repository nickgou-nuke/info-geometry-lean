# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:52.538327+00:00`
Root: `lean/InfoGeometry/Krein/HestenesModularKMSBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **7**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HestenesModularKMSBridge.lean` | `advisory` | 17 | 0 | 7 | 3 | 10 |

## Findings by file

### `lean/InfoGeometry/Krein/HestenesModularKMSBridge.lean`
- module: `InfoGeometry.Krein.HestenesModularKMSBridge`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [soft] `law-field-locker` in `structure-field HestenesKreinKMSPacket.phase_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field HestenesKreinKMSPacket.rotor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field HestenesKreinKMSPacket.rotorInv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field HestenesKreinKMSPacket.modularFlow_eq_rotor_conjugation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field HestenesKreinKMSPacket.rotor_preserves_kreinInner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field HestenesKreinKMSPacket.flow_is_hestenes_analytic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L72 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

