# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:35.645513+00:00`
Root: `lean/InfoGeometry/Automorphic/LanglandsSugawaraBridge.lean`
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
| `lean/InfoGeometry/Automorphic/LanglandsSugawaraBridge.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Automorphic/LanglandsSugawaraBridge.lean`
- module: `InfoGeometry.Automorphic.LanglandsSugawaraBridge`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field LanglandsSugawaraBridge.completedL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field LanglandsSugawaraBridge.centralCharge_eq_completedL_value` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L135 [advisory] `existential-packaging` in `def LanglandsSugawaraBridgeInstalledTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

