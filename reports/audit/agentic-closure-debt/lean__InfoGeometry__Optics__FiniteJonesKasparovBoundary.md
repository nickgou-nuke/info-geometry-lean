# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:27.435663+00:00`
Root: `lean/InfoGeometry/Optics/FiniteJonesKasparovBoundary.lean`
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
| `lean/InfoGeometry/Optics/FiniteJonesKasparovBoundary.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Optics/FiniteJonesKasparovBoundary.lean`
- module: `InfoGeometry.Optics.FiniteJonesKasparovBoundary`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L64 [soft] `skeletal-proof` in `theorem kasparovDefect_eq_one_sub_square` — proof appears to close via minimal tactic one-liner
  - L83 [advisory] `local-hypothesis-injection` in `theorem visibleDefect_eq_kasparovDefect` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L135 [soft] `law-field-locker` in `structure-field FiniteOpticalKernelReadout.modesOfDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field FiniteOpticalKernelReadout.grade` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L154 [soft] `skeletal-proof` in `theorem kernelBasis_eq_modesOf_kasparovDefect` — proof appears to close via minimal tactic one-liner
  - L183 [advisory] `existential-packaging` in `theorem exists_projected_mode_of_index_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

