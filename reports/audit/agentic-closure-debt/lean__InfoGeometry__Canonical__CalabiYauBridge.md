# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:47.111884+00:00`
Root: `lean/InfoGeometry/Canonical/CalabiYauBridge.lean`
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
| `lean/InfoGeometry/Canonical/CalabiYauBridge.lean` | `advisory` | 4 | 0 | 1 | 2 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/CalabiYauBridge.lean`
- module: `InfoGeometry.Canonical.CalabiYauBridge`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field EntropicMetricCanopyPackage.unit_relative_volume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [advisory] `existential-packaging` in `theorem calabiYau_root_factorization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

