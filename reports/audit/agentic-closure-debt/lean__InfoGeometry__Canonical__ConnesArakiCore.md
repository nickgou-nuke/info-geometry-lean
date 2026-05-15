# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:56.078849+00:00`
Root: `lean/InfoGeometry/Canonical/ConnesArakiCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **3**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ConnesArakiCore.lean` | `advisory` | 10 | 0 | 3 | 4 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/ConnesArakiCore.lean`
- module: `InfoGeometry.Canonical.ConnesArakiCore`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field ConnesArakiData.bridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field ConnesArakiData.casini` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field ArakiRelativeEntropyRestrictionDropMonotone.drop_abs_le` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [advisory] `local-hypothesis-injection` in `theorem abs_squeezingLogShear_le_of_abs_time_le_arakiRelativeEntropyDrop` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L141 [advisory] `local-hypothesis-injection` in `theorem abs_squeezingLogShear_le_of_abs_time_le_arakiRelativeEntropyDrop` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L145 [advisory] `local-hypothesis-injection` in `theorem abs_squeezingLogShear_le_of_abs_time_le_arakiRelativeEntropyDrop` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

