# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:09.043682+00:00`
Root: `lean/InfoGeometry/Canonical/VandermondeExclusionBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **3**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/VandermondeExclusionBridge.lean` | `advisory` | 12 | 0 | 3 | 6 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/VandermondeExclusionBridge.lean`
- module: `InfoGeometry.Canonical.VandermondeExclusionBridge`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `law-field-locker` in `structure-field FiniteVandermondeExclusionWitness.nodes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L41 [soft] `section-law-variable` in `variable W` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L70 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L70 [soft] `section-law-variable` in `variable W` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L79 [advisory] `existential-packaging` in `theorem determinant_eq_zero_iff_collision` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L120 [advisory] `bridge-shaped-declaration` in `theorem exclusion_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L120 [advisory] `existential-packaging` in `theorem exclusion_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

