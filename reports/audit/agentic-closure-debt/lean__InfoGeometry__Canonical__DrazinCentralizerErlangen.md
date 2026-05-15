# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:01.783886+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinCentralizerErlangen.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **7**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinCentralizerErlangen.lean` | `advisory` | 19 | 0 | 7 | 5 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinCentralizerErlangen.lean`
- module: `InfoGeometry.Canonical.DrazinCentralizerErlangen`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L64 [soft] `law-field-locker` in `structure-field DrazinCentralizerSanctuary.finite_compressed_weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L131 [advisory] `bridge-shaped-declaration` in `theorem finite_compressed_weight_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L302 [soft] `law-field-locker` in `structure-field DrazinCentralizerFierzLaw.coords` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L305 [soft] `law-field-locker` in `structure-field DrazinCentralizerFierzLaw.coords_eq_expectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L309 [soft] `law-field-locker` in `structure-field DrazinCentralizerFierzLaw.quadric_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L315 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L373 [soft] `law-field-locker` in `structure-field FinalDrazinFierzLaw.coords` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L376 [soft] `law-field-locker` in `structure-field FinalDrazinFierzLaw.coords_are_expectations` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L384 [soft] `law-field-locker` in `structure-field FinalDrazinFierzLaw.quadric_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L390 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

