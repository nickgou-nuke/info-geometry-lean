# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:36.174568+00:00`
Root: `lean/InfoGeometry/Geometry/BilingualUpperHalfPlane.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **5**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/BilingualUpperHalfPlane.lean` | `advisory` | 14 | 0 | 5 | 4 | 9 |

## Findings by file

### `lean/InfoGeometry/Geometry/BilingualUpperHalfPlane.lean`
- module: `InfoGeometry.Geometry.BilingualUpperHalfPlane`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L127 [soft] `law-field-locker` in `structure-field BilingualUpperHalfPlane.K_positivity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L272 [soft] `law-field-locker` in `structure-field MoebiusActionDatum.denom_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L280 [soft] `law-field-locker` in `structure-field MoebiusActionDatum.K_positivity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L320 [soft] `simp-law-injection` in `simp-declaration moebiusMap_tau` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L325 [soft] `skeletal-proof` in `theorem moebiusMap_tau` — proof appears to close via minimal tactic one-liner

