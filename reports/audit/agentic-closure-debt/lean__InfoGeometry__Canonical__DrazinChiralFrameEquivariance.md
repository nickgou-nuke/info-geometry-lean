# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:01.919570+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinChiralFrameEquivariance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **8**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinChiralFrameEquivariance.lean` | `advisory` | 25 | 0 | 8 | 9 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinChiralFrameEquivariance.lean`
- module: `InfoGeometry.Canonical.DrazinChiralFrameEquivariance`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L107 [advisory] `existential-packaging` in `def IsInRegularSector` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L112 [advisory] `existential-packaging` in `def IsInNullSector` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L123 [soft] `law-field-locker` in `structure-field BogoliubovFrameEquiv.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field BogoliubovFrameEquiv.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L125 [soft] `law-field-locker` in `structure-field BogoliubovFrameEquiv.preserves` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field BogoliubovFrameEquiv.preserves_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `skeletal-proof` in `theorem maps_regular_sector` — proof appears to close via minimal tactic one-liner
  - L142 [advisory] `local-hypothesis-injection` in `theorem maps_regular_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L150 [soft] `skeletal-proof` in `theorem maps_null_sector` — proof appears to close via minimal tactic one-liner
  - L160 [advisory] `local-hypothesis-injection` in `theorem maps_null_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L168 [soft] `skeletal-proof` in `theorem inverse_maps_regular_sector` — proof appears to close via minimal tactic one-liner
  - L178 [advisory] `local-hypothesis-injection` in `theorem inverse_maps_regular_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [soft] `skeletal-proof` in `theorem inverse_maps_null_sector` — proof appears to close via minimal tactic one-liner
  - L196 [advisory] `local-hypothesis-injection` in `theorem inverse_maps_null_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

