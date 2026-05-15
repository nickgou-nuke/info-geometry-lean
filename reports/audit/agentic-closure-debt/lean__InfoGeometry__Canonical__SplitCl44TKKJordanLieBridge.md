# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:00.355868+00:00`
Root: `lean/InfoGeometry/Canonical/SplitCl44TKKJordanLieBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **4**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SplitCl44TKKJordanLieBridge.lean` | `advisory` | 14 | 0 | 4 | 6 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/SplitCl44TKKJordanLieBridge.lean`
- module: `InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `skeletal-proof` in `theorem splitCl44_recursive_head_factor` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `skeletal-proof` in `theorem splitCl44_recursive_tail_factor` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `law-field-locker` in `structure-field SplitCl44TKKJordanLiePacket.closure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L119 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L189 [advisory] `bridge-shaped-declaration` in `theorem splitCl44_TKK_JordanLie_constructive_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

