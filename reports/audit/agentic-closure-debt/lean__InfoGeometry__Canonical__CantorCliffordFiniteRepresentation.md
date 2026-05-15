# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:47.822384+00:00`
Root: `lean/InfoGeometry/Canonical/CantorCliffordFiniteRepresentation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **5**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CantorCliffordFiniteRepresentation.lean` | `advisory` | 15 | 0 | 5 | 5 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/CantorCliffordFiniteRepresentation.lean`
- module: `InfoGeometry.Canonical.CantorCliffordFiniteRepresentation`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L79 [soft] `law-field-locker` in `structure-field RealDoubledPhaseAxis.phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field RealDoubledPhaseAxis.phase_sq_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field RealDoubledPhaseAxis.phase_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L350 [soft] `law-field-locker` in `structure-field FiniteCantorCliffordRepresentationPacket.generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L353 [soft] `law-field-locker` in `structure-field FiniteCantorCliffordRepresentationPacket.generator_eq_gamma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L363 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L367 [advisory] `bridge-shaped-declaration` in `theorem generator_eq_gamma_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L384 [advisory] `existential-packaging` in `def FiniteCantorCliffordRepresentationTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

