# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:42.644159+00:00`
Root: `lean/InfoGeometry/Canonical/BerryRotorBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **21**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BerryRotorBridge.lean` | `advisory` | 44 | 0 | 21 | 2 | 23 |

## Findings by file

### `lean/InfoGeometry/Canonical/BerryRotorBridge.lean`
- module: `InfoGeometry.Canonical.BerryRotorBridge`
- status: `advisory`
- debt_score: `44`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L59 [soft] `law-field-locker` in `class-field BivectorPhaseAlgebra.expBiv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `class-field BivectorPhaseAlgebra.exp_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `class-field BivectorPhaseAlgebra.exp_add_of_lie_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `class-field BivectorPhaseAlgebra.phaseLine_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [advisory] `existential-packaging` in `def phaseLine` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L102 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.lineIntegral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.surfaceIntegral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.residue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.holonomy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.lineIntegral_mem_phaseLine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.surfaceIntegral_mem_phaseLine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.residue_mem_phaseLine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.curvature_eq_dA` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.stokes_with_residue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field AbelianModularBerryData.holonomy_is_exp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field NonAbelianSpinBerryData.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field NonAbelianSpinBerryData.holonomy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [soft] `law-field-locker` in `structure-field NonAbelianSpinBerryData.surfaceOrderedExp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field NonAbelianSpinBerryData.anomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field NonAbelianSpinBerryData.curvature_eq_dA_plus_bracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L179 [soft] `law-field-locker` in `structure-field NonAbelianSpinBerryData.nonabelian_stokes_with_anomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

