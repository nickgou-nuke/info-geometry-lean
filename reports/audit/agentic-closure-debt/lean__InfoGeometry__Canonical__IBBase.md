# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:16.488884+00:00`
Root: `lean/InfoGeometry/Canonical/IBBase.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **1**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBBase.lean` | `advisory` | 8 | 0 | 1 | 6 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBBase.lean`
- module: `InfoGeometry.Canonical.IBBase`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field IBProblem.beta_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [advisory] `existential-packaging` in `theorem nonemptyY` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L93 [advisory] `existential-packaging` in `def condYGivenX` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L104 [advisory] `existential-packaging` in `def inducedMProjection` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L203 [advisory] `local-hypothesis-injection` in `lemma baScoreFrozen_slice_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L208 [advisory] `local-hypothesis-injection` in `lemma baScoreFrozen_slice_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

