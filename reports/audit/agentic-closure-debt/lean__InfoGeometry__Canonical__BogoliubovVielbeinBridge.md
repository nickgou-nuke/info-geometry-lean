# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:44.436128+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovVielbeinBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **2**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovVielbeinBridge.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovVielbeinBridge.lean`
- module: `InfoGeometry.Canonical.BogoliubovVielbeinBridge`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L47 [soft] `law-field-locker` in `structure-field BogoliubovVielbeinBridge.frame` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `skeletal-proof` in `theorem phaseCharge_decomposition` — proof appears to close via minimal tactic one-liner

