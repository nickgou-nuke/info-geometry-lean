# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:54.415220+00:00`
Root: `lean/InfoGeometry/Canonical/SYKKitaevGuardrails.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **3**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SYKKitaevGuardrails.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/SYKKitaevGuardrails.lean`
- module: `InfoGeometry.Canonical.SYKKitaevGuardrails`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field TwoCopySYKLikeProtocol.leftHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field TwoCopySYKLikeProtocol.rightHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field TwoCopySYKLikeProtocol.crossCoupling` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [advisory] `existential-packaging` in `def HasTwoCopySYKLikeProtocol` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L66 [advisory] `bridge-shaped-declaration` in `theorem traversableClaimBand_eq_external_of_noProtocol` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L103 [advisory] `existential-packaging` in `theorem exists_weylBoundarySpinorPair_of_kitaevRepoHypotheses` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L115 [advisory] `existential-packaging` in `theorem exists_nontrivial_regularization_pair_of_kitaevRepoHypotheses` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

