# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:22.730670+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SpinBogoliubovStinespring.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **67**
- Hard: **0**
- Soft: **46**
- Advisory: **21**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SpinBogoliubovStinespring.lean` | `advisory` | 113 | 0 | 46 | 21 | 67 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SpinBogoliubovStinespring.lean`
- module: `InfoGeometry.OperatorAlgebra.SpinBogoliubovStinespring`
- status: `advisory`
- debt_score: `113`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `law-field-locker` in `structure-field LocalSpinFrame.admissible_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L73 [soft] `law-field-locker` in `structure-field BogoliubovFrame.annihilator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field BogoliubovFrame.creator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field BogoliubovFrame.bogoliubov_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L106 [soft] `law-field-locker` in `structure-field SpinConnectionTransport.transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field SpinConnectionTransport.preserves_admissibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [soft] `law-field-locker` in `structure-field SpinConnectionTransport.connection_geometry_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L146 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L149 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L189 [soft] `simp-law-injection` in `simp-declaration spinConnectionEndTransport_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L232 [soft] `simp-law-injection` in `simp-declaration canonicalPhaseBogoliubovFrame_annihilator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L239 [soft] `simp-law-injection` in `simp-declaration canonicalPhaseBogoliubovFrame_creator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L278 [soft] `law-field-locker` in `structure-field SpinFrameBogoliubovCalibration.bogoliubovOfFrame` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [soft] `law-field-locker` in `structure-field SpinFrameBogoliubovCalibration.spin_transport_sets_bogoliubov_frame_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L327 [soft] `law-field-locker` in `structure-field BogoliubovFrameMismatch.transportedFrame_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [soft] `law-field-locker` in `structure-field BogoliubovFrameMismatch.sourceBogoliubov_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L343 [soft] `law-field-locker` in `structure-field BogoliubovFrameMismatch.targetBogoliubov_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L347 [soft] `law-field-locker` in `structure-field BogoliubovFrameMismatch.mismatchReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field BogoliubovFrameMismatch.mismatch_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L362 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L403 [soft] `law-field-locker` in `structure-field SpinInducedOpenChannel.channel_from_spin_mismatch_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L418 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L449 [soft] `law-field-locker` in `structure-field SpinBogoliubovStinespringClinch.hidden_component_is_bogoliubov_dual_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L467 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L514 [soft] `law-field-locker` in `structure-field SpinModularCompatibility.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L517 [soft] `law-field-locker` in `structure-field SpinModularCompatibility.modular_flow_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L524 [soft] `law-field-locker` in `structure-field SpinModularCompatibility.spin_modular_covariance_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L538 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L592 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L627 [soft] `law-field-locker` in `structure-field SpinConnectionDatum.valid_spin_connection_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L634 [soft] `law-field-locker` in `structure-field SpinConnectionDatum.induces_bogoliubov_frame_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L645 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L668 [soft] `law-field-locker` in `structure-field SpinModularTransport.modular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L670 [soft] `law-field-locker` in `structure-field SpinModularTransport.spin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L673 [soft] `law-field-locker` in `structure-field SpinModularTransport.modular_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L677 [soft] `law-field-locker` in `structure-field SpinModularTransport.spin_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L685 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L729 [soft] `law-field-locker` in `structure-field LocalChannel.map` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L731 [soft] `law-field-locker` in `structure-field LocalChannel.completelyPositive_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L742 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L769 [soft] `law-field-locker` in `structure-field StinespringLedger.embed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L771 [soft] `law-field-locker` in `structure-field StinespringLedger.compress` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L774 [soft] `law-field-locker` in `structure-field StinespringLedger.globalEvolution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L777 [soft] `law-field-locker` in `structure-field StinespringLedger.channel_factorization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L782 [soft] `law-field-locker` in `structure-field StinespringLedger.leakage` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L785 [soft] `law-field-locker` in `structure-field StinespringLedger.accounting` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L791 [soft] `law-field-locker` in `structure-field StinespringLedger.global_information_preserving_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L805 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L841 [soft] `law-field-locker` in `structure-field GlobalReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L850 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L851 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L884 [soft] `law-field-locker` in `structure-field TomitaRouting.Jconj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L887 [soft] `law-field-locker` in `structure-field TomitaRouting.J_maps_M_to_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L904 [soft] `law-field-locker` in `structure-field StinespringTomitaLedger.embed_mem_M` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L908 [soft] `law-field-locker` in `structure-field StinespringTomitaLedger.leakage_mem_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L919 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L961 [soft] `law-field-locker` in `structure-field SpinBogoliubovStinespringFrame.omega_induces_ledger_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L975 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1011 [soft] `law-field-locker` in `structure-field EinsteinReadoutBridge.curvatureReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1013 [soft] `law-field-locker` in `structure-field EinsteinReadoutBridge.stressReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1019 [soft] `law-field-locker` in `structure-field EinsteinReadoutBridge.einstein_consistency_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1030 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

