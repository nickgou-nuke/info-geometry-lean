# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:43.620623+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/MicroscopicEntropyCalibration.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **48**
- Hard: **0**
- Soft: **34**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/MicroscopicEntropyCalibration.lean` | `advisory` | 82 | 0 | 34 | 14 | 48 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/MicroscopicEntropyCalibration.lean`
- module: `InfoGeometry.SuperMetriplectic.MicroscopicEntropyCalibration`
- status: `advisory`
- debt_score: `82`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field PlanckScaleCalibration.planckLengthSq_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field PlanckScaleCalibration.kB_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field PlanckScaleCalibration.G_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.valid_state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.area` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.mass` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.area_entropy_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.temperature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.temperature_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.mass_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field BlackHoleThermodynamics.area_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L66 [advisory] `local-hypothesis-injection` in `theorem temperature_pos_of_valid_state` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L68 [advisory] `local-hypothesis-injection` in `theorem temperature_pos_of_valid_state` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [advisory] `local-hypothesis-injection` in `theorem temperature_pos_of_valid_state` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L83 [advisory] `local-hypothesis-injection` in `theorem entropy_nonneg_of_valid_state` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L88 [advisory] `existential-packaging` in `structure MicroscopicEntropyCalibration` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [soft] `law-field-locker` in `structure-field MicroscopicEntropyCalibration.microstatesOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `structure-field MicroscopicEntropyCalibration.microEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field MicroscopicEntropyCalibration.entropy_eq_microEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field MicroscopicEntropyCalibration.valid_microEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field MicroscopicEntropyCalibration.microstates_nonempty` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [advisory] `local-hypothesis-injection` in `theorem entropy_nonneg_of_valid_state` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L159 [advisory] `local-hypothesis-injection` in `theorem entropy_nonneg_of_valid_state` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L161 [advisory] `local-hypothesis-injection` in `theorem entropy_nonneg_of_valid_state` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L164 [advisory] `bridge-shaped-declaration` in `theorem entropy_area_count_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L177 [advisory] `local-hypothesis-injection` in `theorem entropy_area_count_packet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L179 [advisory] `local-hypothesis-injection` in `theorem entropy_area_count_packet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L193 [soft] `law-field-locker` in `structure-field HolographicSimulatorCalibration.emergent_geometry_map` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `law-field-locker` in `structure-field RelativeEntropyCalibration.relative_entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [soft] `law-field-locker` in `structure-field RelativeEntropyCalibration.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field RelativeEntropyCalibration.modular_hamiltonian_val` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `law-field-locker` in `structure-field RelativeEntropyCalibration.rel_ent_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field RelativeEntropyCalibration.zero_iff_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L213 [soft] `law-field-locker` in `structure-field RelativeEntropyCalibration.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [advisory] `local-hypothesis-injection` in `theorem modular_energy_self_eq_entropy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L239 [soft] `law-field-locker` in `structure-field RelativeEntropyRestrictionCalibration.restrict` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [soft] `law-field-locker` in `structure-field RelativeEntropyRestrictionCalibration.data_processing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [soft] `law-field-locker` in `structure-field TensorNetworkCutCalibration.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L263 [soft] `law-field-locker` in `structure-field TensorNetworkCutCalibration.cut_capacity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L264 [soft] `law-field-locker` in `structure-field TensorNetworkCutCalibration.admissibleCut` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [soft] `law-field-locker` in `structure-field TensorNetworkCutCalibration.minimalCutOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L266 [soft] `law-field-locker` in `structure-field TensorNetworkCutCalibration.minimalCut_admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L269 [soft] `law-field-locker` in `structure-field TensorNetworkCutCalibration.minimality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L274 [soft] `law-field-locker` in `structure-field TensorNetworkCutCalibration.entanglement_bound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L304 [soft] `law-field-locker` in `structure-field SaturatedTensorNetworkCalibration.saturation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

