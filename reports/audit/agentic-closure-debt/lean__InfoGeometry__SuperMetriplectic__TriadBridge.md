# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:44.526146+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **11**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean` | `advisory` | 25 | 0 | 11 | 3 | 14 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean`
- module: `InfoGeometry.SuperMetriplectic.TriadBridge`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `law-field-locker` in `structure-field DrazinPenroseSchurChiralTriadBridge.translationShadow_eq_effectiveEvenOnsager` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field DrazinPenroseSchurChiralTriadBridge.defectShadow_eq_drazinDefectProjector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L84 [soft] `skeletal-proof` in `theorem toChiralSuperchargeClosure_translationShadow_eq_effectiveEvenOnsager` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `skeletal-proof` in `theorem toChiralSuperchargeClosure_defectShadow_eq_drazinDefectProjector` — proof appears to close via minimal tactic one-liner
  - L128 [soft] `skeletal-proof` in `theorem chiralClosureOfTriadOddData_translationShadow_eq_effectiveEvenOnsager` — proof appears to close via minimal tactic one-liner
  - L154 [soft] `skeletal-proof` in `theorem chiralClosureOfTriadOddData_defectShadow_eq_drazinDefectProjector` — proof appears to close via minimal tactic one-liner
  - L181 [soft] `skeletal-proof` in `theorem toChiralSuperchargeClosure_eq_chiralClosureOfTriadOddData` — proof appears to close via minimal tactic one-liner
  - L222 [soft] `skeletal-proof` in `theorem ofTriadOddData_eq_ofTriadCompatibleOddPacket` — proof appears to close via minimal tactic one-liner
  - L237 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L274 [soft] `skeletal-proof` in `theorem hiddenBlock_chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero` — proof appears to close via minimal tactic one-liner
  - L299 [soft] `skeletal-proof` in `theorem translationReadout_eq_effectiveEvenOnsager` — proof appears to close via minimal tactic one-liner
  - L312 [soft] `skeletal-proof` in `theorem defectReadout_eq_drazinDefectProjector` — proof appears to close via minimal tactic one-liner

