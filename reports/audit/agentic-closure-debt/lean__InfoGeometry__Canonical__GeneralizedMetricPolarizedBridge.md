# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:09.935860+00:00`
Root: `lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean`
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
| `lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean`
- module: `InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `existential-packaging` in `structure GeneralizedMetricPolarizedWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L43 [soft] `law-field-locker` in `structure-field GeneralizedMetricPolarizedWitness.plus_fixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field GeneralizedMetricPolarizedWitness.minus_fixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `simp-law-injection` in `simp-declaration PolarizedRelativeModularPair.plus_lift_fixed_by_tomitaGeneralizedMetric` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration PolarizedRelativeModularPair.minus_lift_fixed_by_tomitaGeneralizedMetric` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

