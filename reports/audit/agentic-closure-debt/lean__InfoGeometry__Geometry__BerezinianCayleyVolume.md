# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:35.585640+00:00`
Root: `lean/InfoGeometry/Geometry/BerezinianCayleyVolume.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **15**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/BerezinianCayleyVolume.lean` | `advisory` | 33 | 0 | 15 | 3 | 18 |

## Findings by file

### `lean/InfoGeometry/Geometry/BerezinianCayleyVolume.lean`
- module: `InfoGeometry.Geometry.BerezinianCayleyVolume`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [soft] `law-field-locker` in `structure-field CayleyDenominator.unit_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field CayleyDiskPoint.cayley_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field SectorSplit.bosonic_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field SectorSplit.fermionic_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field SectorSplit.orthogonal_bf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field SectorSplit.orthogonal_fb` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field SectorSplit.complete` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [soft] `law-field-locker` in `structure-field FredholmDeterminantDatum.admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field FredholmDeterminantDatum.det` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field FredholmDeterminantDatum.det_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L125 [soft] `law-field-locker` in `structure-field FredholmDeterminantDatum.admissible_conj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field FredholmDeterminantDatum.det_conj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field MaxEntBerezinianCalibration.vacuum_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field MaxEntBerezinianCalibration.volume_le_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L187 [soft] `law-field-locker` in `structure-field MaxEntBerezinianCalibration.volume_eq_one_iff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

