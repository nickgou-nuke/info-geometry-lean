# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:56.700131+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauDensityWeightContext.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauDensityWeightContext.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauDensityWeightContext.lean`
- module: `InfoGeometry.Canonical.SouriauDensityWeightContext`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `law-field-locker` in `structure-field SouriauDensityWeightContext.P` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L41 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L61 [soft] `skeletal-proof` in `theorem densityWeight_eq_numberWeight` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem liftedTransportGenerator_eq_souriau_add_number_weighted_dilation` — proof appears to close via minimal tactic one-liner

