# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:01.642525+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinCentralChargeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **0**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinCentralChargeBridge.lean` | `advisory` | 8 | 0 | 0 | 8 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinCentralChargeBridge.lean`
- module: `InfoGeometry.Canonical.DrazinCentralChargeBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L120 [advisory] `existential-packaging` in `theorem exists_internal_split_with_operatorial_shadow` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L162 [advisory] `existential-packaging` in `theorem exists_internal_split_with_intrinsic_nonScalar_shadow` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L257 [advisory] `bridge-shaped-declaration` in `theorem intrinsic_nonScalar_shadow_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L275 [advisory] `bridge-shaped-declaration` in `theorem exists_internal_split_with_intrinsic_nonScalar_shadow_and_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L275 [advisory] `existential-packaging` in `theorem exists_internal_split_with_intrinsic_nonScalar_shadow_and_witness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

