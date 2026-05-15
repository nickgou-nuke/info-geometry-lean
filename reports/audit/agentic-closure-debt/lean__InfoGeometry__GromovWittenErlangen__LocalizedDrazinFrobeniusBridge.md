# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:43.812195+00:00`
Root: `lean/InfoGeometry/GromovWittenErlangen/LocalizedDrazinFrobeniusBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **8**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GromovWittenErlangen/LocalizedDrazinFrobeniusBridge.lean` | `advisory` | 18 | 0 | 8 | 2 | 10 |

## Findings by file

### `lean/InfoGeometry/GromovWittenErlangen/LocalizedDrazinFrobeniusBridge.lean`
- module: `InfoGeometry.GromovWittenErlangen.LocalizedDrazinFrobeniusBridge`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `law-field-locker` in `structure-field FredholmDrazinLocalizationPacket.operatorToAlgebra` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field FredholmDrazinLocalizationPacket.drazin_element_eq_operator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field FredholmDrazinLocalizationPacket.divisorWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field FredholmDrazinLocalizationPacket.divisors_isolate_regular_core_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field FredholmDrazinLocalizationPacket.obstruction_residue_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L145 [soft] `law-field-locker` in `structure-field LocalizedDrazinFrobeniusBridge.fredholm_core_matches_localization_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field LocalizedDrazinFrobeniusBridge.frobenius_self_dual_readout_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field LocalizedDrazinFrobeniusBridge.semisimple_division_blocks_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

