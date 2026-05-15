# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:15.685075+00:00`
Root: `lean/InfoGeometry/Canonical/HorizonZeroModeFierz.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **3**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HorizonZeroModeFierz.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/HorizonZeroModeFierz.lean`
- module: `InfoGeometry.Canonical.HorizonZeroModeFierz`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L131 [soft] `law-field-locker` in `structure-field HorizonZeroModeFierzLaw.coords` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [soft] `law-field-locker` in `structure-field HorizonZeroModeFierzLaw.coords_are_horizon_expectations` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [soft] `law-field-locker` in `structure-field HorizonZeroModeFierzLaw.quadric_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L148 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L164 [advisory] `bridge-shaped-declaration` in `theorem coords_are_horizon_expectations_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

