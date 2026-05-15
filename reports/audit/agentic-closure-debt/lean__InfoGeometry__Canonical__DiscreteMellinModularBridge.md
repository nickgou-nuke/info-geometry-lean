# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:00.692046+00:00`
Root: `lean/InfoGeometry/Canonical/DiscreteMellinModularBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **2**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DiscreteMellinModularBridge.lean` | `advisory` | 8 | 0 | 2 | 4 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/DiscreteMellinModularBridge.lean`
- module: `InfoGeometry.Canonical.DiscreteMellinModularBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `skeletal-proof` in `theorem log_logarithmicSample` — proof appears to close via minimal tactic one-liner
  - L70 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L103 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L104 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L118 [soft] `law-field-locker` in `structure-field OperatorialDiscreteModularHamiltonianContext.commutes_spectralProjectors` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

