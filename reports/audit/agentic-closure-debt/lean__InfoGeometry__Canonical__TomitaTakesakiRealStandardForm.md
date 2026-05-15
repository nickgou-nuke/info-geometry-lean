# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:06.221526+00:00`
Root: `lean/InfoGeometry/Canonical/TomitaTakesakiRealStandardForm.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **7**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TomitaTakesakiRealStandardForm.lean` | `advisory` | 24 | 0 | 7 | 10 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/TomitaTakesakiRealStandardForm.lean`
- module: `InfoGeometry.Canonical.TomitaTakesakiRealStandardForm`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L61 [soft] `skeletal-proof` in `theorem isAntilinearWrt_negAxis_iff` — proof appears to close via minimal tactic one-liner
  - L67 [advisory] `local-hypothesis-injection` in `theorem isAntilinearWrt_negAxis_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [advisory] `local-hypothesis-injection` in `theorem isAntilinearWrt_negAxis_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L73 [advisory] `local-hypothesis-injection` in `theorem isAntilinearWrt_negAxis_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L98 [soft] `law-field-locker` in `structure-field RealStandardForm.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field RealStandardForm.J_left_to_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field RealStandardForm.J_right_to_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L103 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L201 [soft] `skeletal-proof` in `theorem modularTransportFlow_neg_mul` — proof appears to close via minimal tactic one-liner
  - L203 [advisory] `local-hypothesis-injection` in `theorem modularTransportFlow_neg_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L216 [soft] `skeletal-proof` in `theorem modularTransportFlow_mul_neg` — proof appears to close via minimal tactic one-liner
  - L218 [advisory] `local-hypothesis-injection` in `theorem modularTransportFlow_mul_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L253 [advisory] `local-hypothesis-injection` in `theorem orientation_equivalence_package` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

