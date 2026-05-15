# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:58.618749+00:00`
Root: `lean/InfoGeometry/Canonical/DIIIModularEntropyFlowBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **6**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DIIIModularEntropyFlowBridge.lean` | `advisory` | 16 | 0 | 6 | 4 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/DIIIModularEntropyFlowBridge.lean`
- module: `InfoGeometry.Canonical.DIIIModularEntropyFlowBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field ModularDrazinEntropyFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field ModularDrazinEntropyFlow.valid_preserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field ModularDrazinEntropyFlow.entropyTransportLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [advisory] `witness-field-projection` in `structure-field entropyTransport_valid` — witness field `entropyTransport_valid : entropyTransportLaw` detected; verify owner-level derivation
  - L55 [soft] `law-field-locker` in `structure-field ModularDrazinEntropyFlow.entropy_nonneg_preserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L105 [soft] `law-field-locker` in `structure-field DIIIModularEntropyFlowBridge.base` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

