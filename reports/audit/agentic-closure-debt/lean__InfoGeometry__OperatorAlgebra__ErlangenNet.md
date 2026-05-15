# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:13.558766+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ErlangenNet.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **21**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ErlangenNet.lean` | `advisory` | 49 | 0 | 21 | 7 | 28 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ErlangenNet.lean`
- module: `InfoGeometry.OperatorAlgebra.ErlangenNet`
- status: `advisory`
- debt_score: `49`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field LocalObservableFrame.embed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L55 [soft] `skeletal-proof` in `theorem embed_apply` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `law-field-locker` in `structure-field FrameTransformCarrier.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L76 [soft] `skeletal-proof` in `theorem act_apply` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `law-field-locker` in `structure-field LocalSectorSplit.label` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L103 [soft] `skeletal-proof` in `theorem label_apply` — proof appears to close via minimal tactic one-liner
  - L145 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L148 [soft] `skeletal-proof` in `theorem cartan_apply` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `skeletal-proof` in `theorem weylShape_apply` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `skeletal-proof` in `theorem casimir_apply` — proof appears to close via minimal tactic one-liner
  - L174 [soft] `law-field-locker` in `structure-field IteratedObservableSectorization.transition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field IteratedObservableSectorization.finiteCode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [soft] `law-field-locker` in `structure-field IteratedObservableSectorization.boundaryCode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field IteratedObservableSectorization.sectorLabel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L197 [soft] `skeletal-proof` in `theorem finiteCode_apply` — proof appears to close via minimal tactic one-liner
  - L202 [soft] `skeletal-proof` in `theorem boundaryCode_apply` — proof appears to close via minimal tactic one-liner
  - L207 [soft] `skeletal-proof` in `theorem sectorLabel_apply` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `skeletal-proof` in `theorem transition_apply` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `skeletal-proof` in `theorem finiteCode_entry` — proof appears to close via minimal tactic one-liner
  - L222 [soft] `skeletal-proof` in `theorem boundaryCode_entry` — proof appears to close via minimal tactic one-liner
  - L236 [soft] `law-field-locker` in `structure-field WeylRefinedSectorLabel.label` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L245 [soft] `skeletal-proof` in `theorem label_apply` — proof appears to close via minimal tactic one-liner

