# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:23.588179+00:00`
Root: `lean/InfoGeometry/Canonical/KaehlerGeometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **5**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KaehlerGeometry.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/KaehlerGeometry.lean`
- module: `InfoGeometry.Canonical.KaehlerGeometry`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `law-field-locker` in `structure-field KaehlerInformationGeometry.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field KaehlerInformationGeometry.j_sq_eq_neg_id` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field KaehlerInformationGeometry.compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L46 [soft] `simp-law-injection` in `simp-declaration logF_eq_potential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration logF_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

