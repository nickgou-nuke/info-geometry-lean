# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:11.751347+00:00`
Root: `lean/InfoGeometry/Canonical/WeylFiveGradePhysicalReadoutBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **22**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylFiveGradePhysicalReadoutBridge.lean` | `advisory` | 50 | 0 | 22 | 6 | 28 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylFiveGradePhysicalReadoutBridge.lean`
- module: `InfoGeometry.Canonical.WeylFiveGradePhysicalReadoutBridge`
- status: `advisory`
- debt_score: `50`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [soft] `skeletal-proof` in `theorem volume_grade_zero` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `skeletal-proof` in `theorem bkmMass_grade_zero` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `skeletal-proof` in `theorem normalizedCAR_grade_zero` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `skeletal-proof` in `theorem normalizedCCR_grade_zero` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `theorem modularHamiltonianSurrogate_grade_zero` — proof appears to close via minimal tactic one-liner
  - L86 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L89 [soft] `skeletal-proof` in `theorem volume_grade_zero` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `skeletal-proof` in `theorem bkmMass_grade_zero` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `skeletal-proof` in `theorem physicalVolume_apply` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `skeletal-proof` in `theorem physicalMass_apply` — proof appears to close via minimal tactic one-liner
  - L120 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L124 [soft] `skeletal-proof` in `theorem normalizedCAR_grade_zero` — proof appears to close via minimal tactic one-liner
  - L128 [soft] `skeletal-proof` in `theorem normalizedCCR_grade_zero` — proof appears to close via minimal tactic one-liner
  - L157 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L157 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L161 [soft] `skeletal-proof` in `theorem normalizedCAR_grade_zero` — proof appears to close via minimal tactic one-liner
  - L206 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L209 [soft] `skeletal-proof` in `theorem modularHamiltonianSurrogate_grade_zero` — proof appears to close via minimal tactic one-liner
  - L213 [soft] `skeletal-proof` in `theorem Ksur_apply` — proof appears to close via minimal tactic one-liner
  - L240 [soft] `law-field-locker` in `structure-field WeylFiveGradePhysicalReadoutCarrier.fockReadouts` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L247 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L250 [soft] `skeletal-proof` in `theorem volume_grade_zero` — proof appears to close via minimal tactic one-liner
  - L254 [soft] `skeletal-proof` in `theorem bkmMass_grade_zero` — proof appears to close via minimal tactic one-liner
  - L258 [soft] `skeletal-proof` in `theorem normalizedCAR_grade_zero` — proof appears to close via minimal tactic one-liner
  - L262 [soft] `skeletal-proof` in `theorem normalizedCCR_grade_zero` — proof appears to close via minimal tactic one-liner
  - L266 [soft] `skeletal-proof` in `theorem modularHamiltonianSurrogate_grade_zero` — proof appears to close via minimal tactic one-liner

