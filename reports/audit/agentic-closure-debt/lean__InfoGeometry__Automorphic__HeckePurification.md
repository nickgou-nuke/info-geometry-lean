# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:35.230928+00:00`
Root: `lean/InfoGeometry/Automorphic/HeckePurification.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **4**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/HeckePurification.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Automorphic/HeckePurification.lean`
- module: `InfoGeometry.Automorphic.HeckePurification`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L70 [soft] `law-field-locker` in `structure-field HeckeSugawaraIntertwining.intertwining` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field HeckeSugawaraIntertwining.hecke_sugawara_compatibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field HeckeSugawaraIntertwining.completedL_resonance_match` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field HeckeSugawaraIntertwining.purification_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L134 [advisory] `bridge-shaped-declaration` in `theorem hecke_sugawara_compatibility` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L151 [advisory] `existential-packaging` in `theorem langlandsSugawaraBridge_nonempty_of_purification` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

