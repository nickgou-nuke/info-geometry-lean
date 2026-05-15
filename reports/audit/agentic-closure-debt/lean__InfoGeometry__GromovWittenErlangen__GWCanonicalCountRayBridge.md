# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:43.102904+00:00`
Root: `lean/InfoGeometry/GromovWittenErlangen/GWCanonicalCountRayBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **3**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GromovWittenErlangen/GWCanonicalCountRayBridge.lean` | `advisory` | 10 | 0 | 3 | 4 | 7 |

## Findings by file

### `lean/InfoGeometry/GromovWittenErlangen/GWCanonicalCountRayBridge.lean`
- module: `InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [advisory] `existential-packaging` in `structure GWCanonicalCountRayBridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L59 [soft] `law-field-locker` in `structure-field GWCanonicalCountRayBridge.counts_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field GWCanonicalCountRayBridge.ref_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field GWCanonicalCountRayBridge.finiteCarrierShadowLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [advisory] `witness-field-projection` in `structure-field finiteCarrierShadow_valid` — witness field `finiteCarrierShadow_valid : finiteCarrierShadowLaw` detected; verify owner-level derivation
  - L83 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

