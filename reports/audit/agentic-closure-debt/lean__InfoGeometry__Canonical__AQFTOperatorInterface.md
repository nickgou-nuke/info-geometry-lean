# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:37.544771+00:00`
Root: `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **1**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean` | `advisory` | 4 | 0 | 1 | 2 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean`
- module: `InfoGeometry.Canonical.AQFTOperatorInterface`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `law-field-locker` in `structure-field ConcreteInterfacePackage.interpretation_eq_canonical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [advisory] `existential-packaging` in `theorem aqft_root_factorization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

