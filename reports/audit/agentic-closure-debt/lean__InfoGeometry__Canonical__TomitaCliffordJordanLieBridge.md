# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:05.954980+00:00`
Root: `lean/InfoGeometry/Canonical/TomitaCliffordJordanLieBridge.lean`
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
| `lean/InfoGeometry/Canonical/TomitaCliffordJordanLieBridge.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/TomitaCliffordJordanLieBridge.lean`
- module: `InfoGeometry.Canonical.TomitaCliffordJordanLieBridge`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field TomitaCliffordJordanLieBridge.packet` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field TomitaCliffordJordanLieBridge.compact_even_feeds_jordan_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field TomitaCliffordJordanLieBridge.noncompact_odd_feeds_lie_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L76 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L143 [advisory] `bridge-shaped-declaration` in `theorem tomita_clifford_jordan_lie_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L170 [advisory] `existential-packaging` in `def TomitaCliffordJordanLieBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

