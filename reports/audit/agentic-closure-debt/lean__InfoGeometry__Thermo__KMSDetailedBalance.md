# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:47.147761+00:00`
Root: `lean/InfoGeometry/Thermo/KMSDetailedBalance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **7**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/KMSDetailedBalance.lean` | `advisory` | 17 | 0 | 7 | 3 | 10 |

## Findings by file

### `lean/InfoGeometry/Thermo/KMSDetailedBalance.lean`
- module: `InfoGeometry.Thermo.KMSDetailedBalance`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `law-field-locker` in `structure-field KMSRegion.lowerBoundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field KMSRegion.upperBoundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `simp-law-injection` in `simp-declaration standardKMSRegion_lowerBoundary` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `skeletal-proof` in `theorem standardKMSRegion_lowerBoundary` — proof appears to close via minimal tactic one-liner
  - L55 [soft] `simp-law-injection` in `simp-declaration standardKMSRegion_upperBoundary` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `skeletal-proof` in `theorem standardKMSRegion_upperBoundary` — proof appears to close via minimal tactic one-liner
  - L143 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L184 [soft] `law-field-locker` in `structure-field KMSDetailedBalance.form_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

