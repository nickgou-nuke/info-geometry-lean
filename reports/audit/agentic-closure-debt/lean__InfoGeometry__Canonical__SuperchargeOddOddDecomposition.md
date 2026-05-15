# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:04.328630+00:00`
Root: `lean/InfoGeometry/Canonical/SuperchargeOddOddDecomposition.lean`
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
| `lean/InfoGeometry/Canonical/SuperchargeOddOddDecomposition.lean` | `advisory` | 8 | 0 | 2 | 4 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperchargeOddOddDecomposition.lean`
- module: `InfoGeometry.Canonical.SuperchargeOddOddDecomposition`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L57 [soft] `law-field-locker` in `structure-field OddOddDecompositionData.oddOdd_decomposition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L62 [soft] `section-law-variable` in `variable D` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L88 [advisory] `bridge-shaped-declaration` in `theorem oddOdd_decomposition_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

