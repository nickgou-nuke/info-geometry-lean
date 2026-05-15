# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:23.393120+00:00`
Root: `lean/DAG/ProcessFlowExport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/DAG/ProcessFlowExport.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/DAG/ProcessFlowExport.lean`
- module: `DAG.ProcessFlowExport`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L124 [soft] `law-field-locker` in `structure-field FlowEdge.schemaVersion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [soft] `law-field-locker` in `structure-field ProcessEvent.schemaVersion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L160 [soft] `law-field-locker` in `structure-field PathStep.schemaVersion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field Defect.witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field LawfulPathCandidate.schemaVersion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [soft] `law-field-locker` in `structure-field DefectRow.schemaVersion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

