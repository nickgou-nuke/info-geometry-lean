# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:44.912596+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerTriadBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **4**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerTriadBridge.lean` | `advisory` | 13 | 0 | 4 | 5 | 9 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerTriadBridge.lean`
- module: `InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `law-field-locker` in `structure-field UnifiedOwnerTriadCompatibility.owner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field UnifiedOwnerTriadCompatibility.translationReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field UnifiedOwnerTriadCompatibility.defectReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L65 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L116 [advisory] `bridge-shaped-declaration` in `theorem ownerTriadCompatibility_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

