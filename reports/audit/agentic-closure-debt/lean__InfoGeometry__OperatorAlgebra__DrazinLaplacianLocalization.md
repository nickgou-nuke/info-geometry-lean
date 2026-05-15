# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:12.997149+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/DrazinLaplacianLocalization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **10**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/DrazinLaplacianLocalization.lean` | `advisory` | 23 | 0 | 10 | 3 | 13 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/DrazinLaplacianLocalization.lean`
- module: `InfoGeometry.OperatorAlgebra.DrazinLaplacianLocalization`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `law-field-locker` in `structure-field DrazinLaplacianCalibration.laplacian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field DrazinLaplacianCalibration.laplacian_eq_element` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field DrazinLaplacianCalibration.eulerWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field DrazinLaplacianCalibration.eulerWeight_eq_stableVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L119 [soft] `law-field-locker` in `structure-field GWDrazinLaplacianBridge.edgeState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field GWDrazinLaplacianBridge.edge_valid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field GWDrazinLaplacianBridge.edgeEulerWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L129 [soft] `law-field-locker` in `structure-field GWDrazinLaplacianBridge.edgeEulerWeight_eq_laplacianWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [soft] `law-field-locker` in `structure-field GWDrazinLaplacianBridge.edgeContributionReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L136 [soft] `law-field-locker` in `structure-field GWDrazinLaplacianBridge.edgeContribution_eq_entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

