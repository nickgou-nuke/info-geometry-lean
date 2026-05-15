# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:49.376935+00:00`
Root: `lean/InfoGeometry/Canonical/RealTomitaCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **8**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealTomitaCore.lean` | `advisory` | 22 | 0 | 8 | 6 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealTomitaCore.lean`
- module: `InfoGeometry.Canonical.RealTomitaCore`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L64 [soft] `law-field-locker` in `structure-field RealModularLogData.exp_deltaLog` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L67 [soft] `section-law-variable` in `variable T` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L84 [soft] `simp-law-injection` in `simp-declaration flow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L92 [soft] `skeletal-proof` in `theorem flow_add` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `skeletal-proof` in `theorem flow_neg_mul` — proof appears to close via minimal tactic one-liner
  - L99 [advisory] `local-hypothesis-injection` in `theorem flow_neg_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L113 [soft] `skeletal-proof` in `theorem flow_mul_neg` — proof appears to close via minimal tactic one-liner
  - L115 [advisory] `local-hypothesis-injection` in `theorem flow_mul_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L127 [soft] `simp-law-injection` in `simp-declaration adjointFlow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `skeletal-proof` in `theorem flow_negLog_eq_time_reverse` — proof appears to close via minimal tactic one-liner

