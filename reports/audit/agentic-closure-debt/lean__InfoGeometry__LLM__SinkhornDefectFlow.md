# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:57.660474+00:00`
Root: `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **52**
- Hard: **0**
- Soft: **34**
- Advisory: **18**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean` | `advisory` | 86 | 0 | 34 | 18 | 52 |

## Findings by file

### `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean`
- module: `InfoGeometry.LLM.SinkhornDefectFlow`
- status: `advisory`
- debt_score: `86`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L88 [soft] `simp-law-injection` in `simp-declaration ofZDControlledObserver_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `law-field-locker` in `structure-field SinkhornDefectStep.next` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L171 [soft] `simp-law-injection` in `simp-declaration SinkhornDefectStep.of_routerResidual_eq_zero_next` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L177 [soft] `skeletal-proof` in `theorem sourcedGenerator_deviation_next_le_of_routerResidual_eq_zero` — proof appears to close via minimal tactic one-liner
  - L195 [soft] `law-field-locker` in `structure-field SinkhornThermodynamicDefectStep.next` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [soft] `law-field-locker` in `structure-field RouterClockDefectBridge.bound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `law-field-locker` in `structure-field RouterClockDefectBridge.residual_eq_clockDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [soft] `simp-law-injection` in `simp-declaration ofCanonicalClockDefect_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L287 [soft] `simp-law-injection` in `simp-declaration ofDetailedEquilibrium_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L299 [soft] `simp-law-injection` in `simp-declaration ofDetailedEquilibrium_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L310 [soft] `skeletal-proof` in `theorem ofDetailedEquilibrium_isRouterEquilibrium` — proof appears to close via minimal tactic one-liner
  - L416 [soft] `law-field-locker` in `structure-field SinkhornDefectUpdate.map` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L428 [soft] `simp-law-injection` in `simp-declaration iterate_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L433 [soft] `simp-law-injection` in `simp-declaration iterate_succ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L582 [soft] `skeletal-proof` in `theorem dissipatedHeatRN_nonneg` — proof appears to close via minimal tactic one-liner
  - L619 [soft] `law-field-locker` in `structure-field SinkhornVolumeAnomalyBridge.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L620 [soft] `law-field-locker` in `structure-field SinkhornVolumeAnomalyBridge.next_le_volumeNext` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L622 [soft] `law-field-locker` in `structure-field SinkhornVolumeAnomalyBridge.volume_le_now` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L641 [soft] `law-field-locker` in `structure-field SinkhornThermodynamicRelativeDefectBridge.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L642 [soft] `law-field-locker` in `structure-field SinkhornThermodynamicRelativeDefectBridge.next_le_volumeNext` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L644 [soft] `law-field-locker` in `structure-field SinkhornThermodynamicRelativeDefectBridge.volume_le_now` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L656 [soft] `law-field-locker` in `structure-field SinkhornRNBarrierThermodynamicComparison.B` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L659 [soft] `law-field-locker` in `structure-field SinkhornRNBarrierThermodynamicComparison.residual_readout_eq_barrier` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L661 [soft] `law-field-locker` in `structure-field SinkhornRNBarrierThermodynamicComparison.central_readout_budget` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L685 [soft] `simp-law-injection` in `simp-declaration SinkhornRNBarrierThermodynamicComparison.ofResidualReadoutEqBarrier_central_readout_budget` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L707 [advisory] `existential-packaging` in `structure SinkhornRNBarrierProfileLift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L725 [soft] `law-field-locker` in `structure-field SinkhornRNBarrierProfileLift.scale_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L728 [soft] `law-field-locker` in `structure-field SinkhornRNBarrierProfileLift.rnBarrier_eq_scaled_informationGeometricRelativeNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L733 [advisory] `existential-packaging` in `structure PhaseRNBarrierProfileLift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L749 [soft] `law-field-locker` in `structure-field PhaseRNBarrierProfileLift.scale_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L752 [soft] `law-field-locker` in `structure-field PhaseRNBarrierProfileLift.phaseRNBarrier_eq_scaled_informationGeometricRelativeNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L780 [advisory] `existential-packaging` in `theorem countMass_unitCounts` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L780 [soft] `skeletal-proof` in `theorem countMass_unitCounts` — proof appears to close via minimal tactic one-liner
  - L786 [advisory] `existential-packaging` in `structure RowRNBarrierCountProfileLift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L800 [soft] `law-field-locker` in `structure-field RowRNBarrierCountProfileLift.scale_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L801 [soft] `law-field-locker` in `structure-field RowRNBarrierCountProfileLift.rowRNBarrier_eq_scaled_informationGeometricRelativeNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L807 [advisory] `existential-packaging` in `structure ColRNBarrierCountProfileLift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L817 [soft] `law-field-locker` in `structure-field ColRNBarrierCountProfileLift.scale_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L818 [soft] `law-field-locker` in `structure-field ColRNBarrierCountProfileLift.colRNBarrier_eq_scaled_informationGeometricRelativeNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L824 [advisory] `existential-packaging` in `def RowRNBarrierCountProfileLift.ofMassNormalized` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L849 [advisory] `local-hypothesis-injection` in `def RowRNBarrierCountProfileLift.ofMassNormalized` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L851 [advisory] `local-hypothesis-injection` in `def RowRNBarrierCountProfileLift.ofMassNormalized` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L854 [advisory] `local-hypothesis-injection` in `def RowRNBarrierCountProfileLift.ofMassNormalized` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L876 [advisory] `existential-packaging` in `def ColRNBarrierCountProfileLift.ofMassNormalized` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L896 [advisory] `local-hypothesis-injection` in `def ColRNBarrierCountProfileLift.ofMassNormalized` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L898 [advisory] `local-hypothesis-injection` in `def ColRNBarrierCountProfileLift.ofMassNormalized` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L901 [advisory] `local-hypothesis-injection` in `def ColRNBarrierCountProfileLift.ofMassNormalized` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L923 [advisory] `existential-packaging` in `def PhaseRNBarrierProfileLift.ofRowCounts` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L945 [advisory] `existential-packaging` in `def PhaseRNBarrierProfileLift.ofColCounts` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

