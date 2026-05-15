# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:23.393243+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/StinespringDilation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **63**
- Hard: **0**
- Soft: **54**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/StinespringDilation.lean` | `advisory` | 117 | 0 | 54 | 9 | 63 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/StinespringDilation.lean`
- module: `InfoGeometry.OperatorAlgebra.StinespringDilation`
- status: `advisory`
- debt_score: `117`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `law-field-locker` in `structure-field BregmanBackend.div` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field BregmanBackend.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field BregmanBackend.self_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field OpenSystemChannel.actual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field OpenSystemChannel.ideal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field OpenSystemChannel.actual_preserves_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field OpenSystemChannel.ideal_preserves_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field StinespringDilation.embedSystem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field StinespringDilation.jointEvolution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field StinespringDilation.reduceSystem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field StinespringDilation.hiddenLeak` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field StinespringDilation.mirrorLeak` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field StinespringDilation.actual_eq_reduced` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `law-field-locker` in `structure-field StinespringDilation.conservation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field StinespringDilation.dilation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L241 [soft] `law-field-locker` in `structure-field HiddenInformationReadout.hiddenInfo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field HiddenInformationReadout.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L296 [soft] `law-field-locker` in `structure-field HeatHiddenInformationBridge.heat_eq_hidden` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L302 [soft] `law-field-locker` in `structure-field HeatHiddenInformationBridge.thermodynamic_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [soft] `law-field-locker` in `structure-field MetalMirrorStinespringModel.metal_mirror_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L382 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L426 [soft] `law-field-locker` in `structure-field DissipativeChannel.actual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L427 [soft] `law-field-locker` in `structure-field DissipativeChannel.ideal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L451 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.hiddenFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L454 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.recoverHidden` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L457 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.conservation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L464 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.tomita_commutant_routing_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L474 [soft] `law-field-locker` in `structure-field StinespringTomitaDilation.hidden_inaccessible_to_visible_observer_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L530 [soft] `law-field-locker` in `structure-field BregmanDivergenceDatum.div` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L531 [soft] `law-field-locker` in `structure-field BregmanDivergenceDatum.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L534 [soft] `law-field-locker` in `structure-field BregmanDivergenceDatum.self_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L612 [soft] `law-field-locker` in `structure-field HeatEqualsHiddenInformation.heat_eq_hidden` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L675 [soft] `law-field-locker` in `structure-field DistinguishabilityDatum.distinguish` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L676 [soft] `law-field-locker` in `structure-field DistinguishabilityDatum.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L688 [soft] `law-field-locker` in `structure-field VisibleDistinguishabilityLoss.actual_le_ideal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L736 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.inject` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L739 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.systemPart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L742 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.environmentPart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L745 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.dilatedFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L748 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.observedFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L751 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.observed_factorization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L756 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.systemPart_inject` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L761 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.accessibleInfo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L764 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.hiddenInfo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L767 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.totalInfo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L770 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.total_split` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L777 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.total_conserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L783 [soft] `law-field-locker` in `structure-field StinespringInformationDilation.environment_initial_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L796 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L813 [advisory] `local-hypothesis-injection` in `theorem accessible_loss_eq_hidden_information` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L829 [advisory] `local-hypothesis-injection` in `theorem accessible_loss_eq_hidden_information` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L846 [soft] `law-field-locker` in `structure-field HeatCalibration.heat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L848 [soft] `law-field-locker` in `structure-field HeatCalibration.heat_eq_accessible_loss` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L858 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L882 [soft] `law-field-locker` in `structure-field BregmanHeatCalibration.idealFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L884 [soft] `law-field-locker` in `structure-field BregmanHeatCalibration.bregman` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L887 [soft] `law-field-locker` in `structure-field BregmanHeatCalibration.bregman_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L891 [soft] `law-field-locker` in `structure-field BregmanHeatCalibration.bregman_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L895 [soft] `law-field-locker` in `structure-field BregmanHeatCalibration.heat_eq_bregman` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L907 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L980 [advisory] `existential-packaging` in `def StinespringInformationDilationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

