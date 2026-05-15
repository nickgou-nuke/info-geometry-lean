# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:56.830590+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauFenchelOnsagerBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **7**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauFenchelOnsagerBridge.lean` | `advisory` | 20 | 0 | 7 | 6 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauFenchelOnsagerBridge.lean`
- module: `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L50 [soft] `law-field-locker` in `structure-field CoadjointMomentMapData.moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field CoadjointMomentMapData.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L65 [soft] `skeletal-proof` in `theorem actionAt_eq_pairing` — proof appears to close via minimal tactic one-liner
  - L83 [advisory] `existential-packaging` in `structure SouriauFenchelContext` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L88 [soft] `law-field-locker` in `structure-field SouriauFenchelContext.massieu_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L94 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L98 [soft] `skeletal-proof` in `theorem partition_eq_exp_souriauMassieu` — proof appears to close via minimal tactic one-liner
  - L136 [advisory] `existential-packaging` in `theorem scaledFenchelGap_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L148 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L148 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

