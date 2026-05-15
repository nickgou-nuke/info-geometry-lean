# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:15.547158+00:00`
Root: `lean/InfoGeometry/Canonical/HorizonStringDiagram.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **14**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HorizonStringDiagram.lean` | `advisory` | 32 | 0 | 14 | 4 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/HorizonStringDiagram.lean`
- module: `InfoGeometry.Canonical.HorizonStringDiagram`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field HorizonStringDiagram.source` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field HorizonStringDiagram.sink` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field HorizonStringDiagram.mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field HorizonStringDiagram.edgeLabel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field HorizonStringDiagram.edgeWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [soft] `skeletal-proof` in `theorem source_apply` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `skeletal-proof` in `theorem sink_apply` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem mirror_apply` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `skeletal-proof` in `theorem edgeLabel_apply` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `skeletal-proof` in `theorem edgeWeight_apply` — proof appears to close via minimal tactic one-liner
  - L114 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L117 [soft] `skeletal-proof` in `theorem diagram_apply` — proof appears to close via minimal tactic one-liner
  - L121 [soft] `skeletal-proof` in `theorem homogeneousReadout_apply` — proof appears to close via minimal tactic one-liner
  - L149 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L152 [soft] `skeletal-proof` in `theorem diagram_apply` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `skeletal-proof` in `theorem flowGenerator_apply` — proof appears to close via minimal tactic one-liner

