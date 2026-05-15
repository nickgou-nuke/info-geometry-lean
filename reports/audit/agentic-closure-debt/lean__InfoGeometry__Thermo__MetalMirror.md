# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:47.287697+00:00`
Root: `lean/InfoGeometry/Thermo/MetalMirror.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **56**
- Hard: **0**
- Soft: **51**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/MetalMirror.lean` | `advisory` | 107 | 0 | 51 | 5 | 56 |

## Findings by file

### `lean/InfoGeometry/Thermo/MetalMirror.lean`
- module: `InfoGeometry.Thermo.MetalMirror`
- status: `advisory`
- debt_score: `107`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L56 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.actualFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.idealFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.actual_preserves_cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.ideal_preserves_cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.actual_dissipative_branch_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.ideal_lossless_branch_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `simp-law-injection` in `simp-declaration actualPoint_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `skeletal-proof` in `theorem actualPoint_op` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `simp-law-injection` in `simp-declaration idealPoint_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `skeletal-proof` in `theorem idealPoint_op` — proof appears to close via minimal tactic one-liner
  - L136 [soft] `law-field-locker` in `structure-field StinespringTomitaMirrorDilation.mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field StinespringTomitaMirrorDilation.leakFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field StinespringTomitaMirrorDilation.conservation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L146 [soft] `law-field-locker` in `structure-field StinespringTomitaMirrorDilation.tomita_mirror_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field StinespringTomitaMirrorDilation.dilation_conservation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [soft] `law-field-locker` in `structure-field MetalMirrorRicciFluxBridge.sourceLeft` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [soft] `law-field-locker` in `structure-field MetalMirrorRicciFluxBridge.sourceRight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L286 [soft] `law-field-locker` in `structure-field MetalMirrorRicciFluxBridge.heat_eq_ricci_flux` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [soft] `law-field-locker` in `structure-field MetalMirrorRicciFluxBridge.bregman_bridge_compatibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [advisory] `existential-packaging` in `def MetalMirrorChannelOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L334 [advisory] `existential-packaging` in `def StinespringTomitaMirrorDilationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L340 [advisory] `existential-packaging` in `def MetalMirrorRicciFluxBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L383 [soft] `simp-law-injection` in `simp-declaration coe_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L385 [soft] `skeletal-proof` in `theorem coe_mk` — proof appears to close via minimal tactic one-liner
  - L405 [soft] `law-field-locker` in `structure-field BregmanDivergenceDatum.div` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L406 [soft] `law-field-locker` in `structure-field BregmanDivergenceDatum.nonneg_on_cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L412 [soft] `law-field-locker` in `structure-field BregmanDivergenceDatum.self_eq_zero_on_cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L432 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.actualFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L433 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.idealUnitary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L434 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.actual_preserves_cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L439 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.ideal_preserves_cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L444 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.actual_dissipative_branch_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L451 [soft] `law-field-locker` in `structure-field MetalMirrorChannel.ideal_lossless_branch_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L494 [soft] `law-field-locker` in `structure-field StinespringMirrorDilation.mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L495 [soft] `law-field-locker` in `structure-field StinespringMirrorDilation.commutantFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L496 [soft] `law-field-locker` in `structure-field StinespringMirrorDilation.conservation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L588 [soft] `law-field-locker` in `structure-field RicciFluxReadout.flux` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L601 [soft] `law-field-locker` in `structure-field MetalMirrorHeatRicciFluxBridge.heat_eq_flux` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L604 [soft] `law-field-locker` in `structure-field MetalMirrorHeatRicciFluxBridge.tkk_grade_slippage_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L610 [soft] `law-field-locker` in `structure-field MetalMirrorHeatRicciFluxBridge.bregman_hessian_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L645 [soft] `law-field-locker` in `structure-field MetalMirrorOpticalCalibration.reflectivity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L646 [soft] `law-field-locker` in `structure-field MetalMirrorOpticalCalibration.retardance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L647 [soft] `law-field-locker` in `structure-field MetalMirrorOpticalCalibration.ellipticity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L648 [soft] `law-field-locker` in `structure-field MetalMirrorOpticalCalibration.refractiveIndexReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L649 [soft] `law-field-locker` in `structure-field MetalMirrorOpticalCalibration.heat_controls_absorption_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L652 [soft] `law-field-locker` in `structure-field MetalMirrorOpticalCalibration.hessian_controls_retardance_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L655 [soft] `law-field-locker` in `structure-field MetalMirrorOpticalCalibration.retardance_controls_ellipticity_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L659 [soft] `law-field-locker` in `structure-field MetalMirrorOpticalCalibration.refractive_index_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L676 [soft] `law-field-locker` in `structure-field MetalMirrorThermoReadout.heatFlux` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L677 [soft] `law-field-locker` in `structure-field MetalMirrorThermoReadout.heatFlux_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L703 [soft] `law-field-locker` in `structure-field MetalMirrorRicciFluxAdmissible.ricciFlux` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L704 [soft] `law-field-locker` in `structure-field MetalMirrorRicciFluxAdmissible.heat_eq_ricciFlux` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L708 [soft] `law-field-locker` in `structure-field MetalMirrorRicciFluxAdmissible.tkk_grade_slippage_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L711 [soft] `law-field-locker` in `structure-field MetalMirrorRicciFluxAdmissible.bregman_hessian_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L714 [advisory] `existential-packaging` in `theorem metalMirrorRicciFluxBridge_nonempty_of_admissible` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

