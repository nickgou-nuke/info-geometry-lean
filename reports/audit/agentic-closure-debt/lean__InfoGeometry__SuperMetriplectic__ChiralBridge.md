# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:41.954197+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/ChiralBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **7**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/ChiralBridge.lean` | `advisory` | 18 | 0 | 7 | 4 | 11 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/ChiralBridge.lean`
- module: `InfoGeometry.SuperMetriplectic.ChiralBridge`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [soft] `law-field-locker` in `structure-field DrazinChiralSuperchargeClosureBridge.U` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L43 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L74 [soft] `skeletal-proof` in `theorem toChiralSuperchargeClosure_leftShadow_eq_QL` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `theorem toChiralSuperchargeClosure_rightShadow_eq_QR` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `skeletal-proof` in `theorem toChiralSuperchargeClosure_netOddShadow_eq_QD` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `skeletal-proof` in `theorem toChiralSuperchargeClosure_translationShadow_eq_drazinTranslationCandidate` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `skeletal-proof` in `theorem toChiralSuperchargeClosure_defectShadow_eq_drazinCentralCandidate` — proof appears to close via minimal tactic one-liner

