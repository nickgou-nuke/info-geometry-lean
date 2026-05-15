# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:40.722763+00:00`
Root: `lean/InfoGeometry/Canonical/PauliHestenesSpinMomentum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **69**
- Hard: **0**
- Soft: **52**
- Advisory: **17**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PauliHestenesSpinMomentum.lean` | `advisory` | 121 | 0 | 52 | 17 | 69 |

## Findings by file

### `lean/InfoGeometry/Canonical/PauliHestenesSpinMomentum.lean`
- module: `InfoGeometry.Canonical.PauliHestenesSpinMomentum`
- status: `advisory`
- debt_score: `121`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L64 [soft] `skeletal-proof` in `theorem det_pauliMatrix_eq_minkowskiNormSq` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `skeletal-proof` in `theorem trace_pauliMatrix_eq_two_energy` — proof appears to close via minimal tactic one-liner
  - L193 [soft] `skeletal-proof` in `theorem onMassShell_zero_iff_isNull` — proof appears to close via minimal tactic one-liner
  - L215 [soft] `law-field-locker` in `structure-field PauliParavectorBridge.pauliMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L217 [soft] `law-field-locker` in `structure-field PauliParavectorBridge.minkowskiNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field PauliParavectorBridge.det` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field PauliParavectorBridge.det_pauliMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L279 [soft] `law-field-locker` in `structure-field LorentzSpinActionBridge.actVector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [soft] `law-field-locker` in `structure-field LorentzSpinActionBridge.actHermitian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [soft] `law-field-locker` in `structure-field LorentzSpinActionBridge.pauliMap_equivariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L289 [soft] `law-field-locker` in `structure-field LorentzSpinActionBridge.det_preserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L294 [soft] `law-field-locker` in `structure-field LorentzSpinActionBridge.double_cover_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L310 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L354 [soft] `law-field-locker` in `structure-field SpinorHelicityFactorization.momentumOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L356 [soft] `law-field-locker` in `structure-field SpinorHelicityFactorization.outerProduct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L359 [soft] `law-field-locker` in `structure-field SpinorHelicityFactorization.pauli_eq_outerProduct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L364 [soft] `law-field-locker` in `structure-field SpinorHelicityFactorization.momentum_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [soft] `law-field-locker` in `structure-field SpinorHelicityFactorization.orientation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L380 [soft] `law-field-locker` in `structure-field SpinorHelicityFactorization.rank_one_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L392 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L429 [soft] `law-field-locker` in `structure-field PauliParavectorDatum.determinant_metric_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L440 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L466 [soft] `law-field-locker` in `structure-field SpinMomentumFrame.momentum_transport_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L473 [soft] `law-field-locker` in `structure-field SpinMomentumFrame.spin_transport_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L484 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L512 [soft] `law-field-locker` in `structure-field LorentzSpinRepresentationCoupling.actMomentum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L516 [soft] `law-field-locker` in `structure-field LorentzSpinRepresentationCoupling.actSpinBivector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L520 [soft] `law-field-locker` in `structure-field LorentzSpinRepresentationCoupling.shared_spin_action_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L532 [soft] `law-field-locker` in `structure-field LorentzSpinRepresentationCoupling.representation_coupling_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L548 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L573 [soft] `law-field-locker` in `structure-field MasslessSpinMomentumFrame.detP_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L577 [soft] `law-field-locker` in `structure-field MasslessSpinMomentumFrame.helicity_locked_to_momentum_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L588 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L617 [soft] `law-field-locker` in `structure-field HestenesSpinorRotorDatum.momentumReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L619 [soft] `law-field-locker` in `structure-field HestenesSpinorRotorDatum.rotorReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L622 [soft] `law-field-locker` in `structure-field HestenesSpinorRotorDatum.spinBivector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L625 [soft] `law-field-locker` in `structure-field HestenesSpinorRotorDatum.momentum_readout_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L632 [soft] `law-field-locker` in `structure-field HestenesSpinorRotorDatum.spin_bivector_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L639 [soft] `law-field-locker` in `structure-field HestenesSpinorRotorDatum.rotor_transport_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L650 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L681 [soft] `law-field-locker` in `structure-field SpinMomentumBridge.momentumOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L683 [soft] `law-field-locker` in `structure-field SpinMomentumBridge.spinPlaneOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L686 [soft] `law-field-locker` in `structure-field SpinMomentumBridge.minkowskiNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L689 [soft] `law-field-locker` in `structure-field SpinMomentumBridge.spinorNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L692 [soft] `law-field-locker` in `structure-field SpinMomentumBridge.mass_shell` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L702 [soft] `law-field-locker` in `structure-field SpinMomentumBridge.sameRotorFrame_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L713 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L738 [soft] `law-field-locker` in `structure-field MasslessSpinMomentumBranch.nullMomentumCondition_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L749 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L775 [soft] `law-field-locker` in `structure-field CovariantSpinorRotorReadouts.common_source_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L782 [soft] `law-field-locker` in `structure-field CovariantSpinorRotorReadouts.distinct_readout_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L798 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L837 [soft] `law-field-locker` in `structure-field UncertaintyReadoutGuard.noncommuting_pair_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L848 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L868 [soft] `law-field-locker` in `structure-field SpinMomentumCoupling.invariantReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L870 [soft] `law-field-locker` in `structure-field SpinMomentumCoupling.momentum_spin_coupling_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L883 [soft] `law-field-locker` in `structure-field SpinMomentumCoupling.frame_transport_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L899 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L923 [soft] `law-field-locker` in `structure-field HelicityCalibration.helicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L925 [soft] `law-field-locker` in `structure-field HelicityCalibration.null_momentum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L929 [soft] `law-field-locker` in `structure-field HelicityCalibration.helicity_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L946 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L978 [soft] `law-field-locker` in `structure-field ChiralLightconeReadoutDatum.Lightcone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L989 [advisory] `existential-packaging` in `structure PauliHestenesChiralLightconeBridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L993 [soft] `law-field-locker` in `structure-field PauliHestenesChiralLightconeBridge.carrierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L995 [soft] `law-field-locker` in `structure-field PauliHestenesChiralLightconeBridge.null_momentum_hits_chiral_lightcone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1013 [advisory] `existential-packaging` in `theorem chiral_lightcone_readout_of_null_momentum` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

