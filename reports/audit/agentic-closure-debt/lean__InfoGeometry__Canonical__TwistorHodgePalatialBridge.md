# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:07.410921+00:00`
Root: `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **10**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean` | `advisory` | 24 | 0 | 10 | 4 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean`
- module: `InfoGeometry.Canonical.TwistorHodgePalatialBridge`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L57 [soft] `law-field-locker` in `structure-field HodgeStarSelfDualSplit.selfDualCondition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field HodgeStarSelfDualSplit.antiSelfDualCondition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field HodgeStarSelfDualSplit.incidenceCompatible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field PalatialTwistorOperatorAlgebra.operatorialIncidence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field PalatialTwistorOperatorAlgebra.differentialOperatorCompatible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field PalatialTwistorOperatorAlgebra.incidenceHolonomyCompatible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [soft] `law-field-locker` in `structure-field TwistorHodgePalatialBridgeContext.incidenceTransportCompatible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `law-field-locker` in `structure-field TwistorHodgePalatialBridgeContext.hodgeHolonomyCompatible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field TwistorHodgePalatialBridgeContext.operatorHodgeCompatible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [advisory] `bridge-shaped-declaration` in `theorem TwistorHodgePalatialBridgeContext.combined_compatibility` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L156 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L158 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L180 [soft] `skeletal-proof` in `theorem palatialOperatorAlgebraOfCertifiedConformalInference_operatorialIncidence` — proof appears to close via minimal tactic one-liner

