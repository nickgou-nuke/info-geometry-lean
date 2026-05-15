# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:03.295591+00:00`
Root: `lean/InfoGeometry/Meta/GromovErgostructureBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **4**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Meta/GromovErgostructureBridge.lean` | `advisory` | 16 | 0 | 4 | 8 | 12 |

## Findings by file

### `lean/InfoGeometry/Meta/GromovErgostructureBridge.lean`
- module: `InfoGeometry.Meta.GromovErgostructureBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L52 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L66 [advisory] `existential-packaging` in `structure BayesRouterCertification` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L83 [soft] `law-field-locker` in `structure-field BayesRouterCertification.x` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L127 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L127 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L146 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L146 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L155 [advisory] `existential-packaging` in `structure GromovErgostructureHandoff` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L179 [soft] `law-field-locker` in `structure-field GromovErgostructureHandoff.majorana` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L217 [advisory] `existential-packaging` in `def GromovErgostructureBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

