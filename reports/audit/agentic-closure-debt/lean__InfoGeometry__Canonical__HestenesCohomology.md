# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:13.522520+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesCohomology.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **6**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesCohomology.lean` | `advisory` | 17 | 0 | 6 | 5 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesCohomology.lean`
- module: `InfoGeometry.Canonical.HestenesCohomology`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `law-field-locker` in `structure-field HestenesCochainOperator.kLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field HestenesAnticohainOperator.kAntilinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `skeletal-proof` in `theorem isHestenesCochainOperator_iff_analyticSymmetry` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `skeletal-proof` in `theorem zero_isHestenesCochainOperator` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `theorem id_isHestenesCochainOperator` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `skeletal-proof` in `theorem comp_isHestenesCochainOperator` — proof appears to close via minimal tactic one-liner
  - L150 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L185 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

