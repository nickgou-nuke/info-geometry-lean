# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:28.198384+00:00`
Root: `lean/InfoGeometry/Canonical/MasterSynthesis.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **87**
- Hard: **0**
- Soft: **24**
- Advisory: **63**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/MasterSynthesis.lean` | `advisory` | 111 | 0 | 24 | 63 | 87 |

## Findings by file

### `lean/InfoGeometry/Canonical/MasterSynthesis.lean`
- module: `InfoGeometry.Canonical.MasterSynthesis`
- status: `advisory`
- debt_score: `111`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L89 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L97 [advisory] `bridge-shaped-declaration` in `theorem anomalyExclusion_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L97 [advisory] `existential-packaging` in `theorem anomalyExclusion_witness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [advisory] `existential-packaging` in `theorem anomalyExclusion_package_of_chiralAnomaly_eq_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L124 [advisory] `existential-packaging` in `theorem anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L145 [advisory] `existential-packaging` in `theorem anomalyExclusion_package_of_unitRelativeVolumeBit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L199 [soft] `law-field-locker` in `structure-field MatchedHelicityWitness.omega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [soft] `law-field-locker` in `structure-field MatchedHelicityWitness.Omega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [soft] `law-field-locker` in `structure-field MatchedHelicityWitness.match_helicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field ZPEGravityWitness.hRankPos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field ThermalBottWitness.V` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `law-field-locker` in `structure-field ThermalBottWitness.hCompat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L255 [soft] `law-field-locker` in `structure-field RegularizationWitness.h_star` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L269 [soft] `law-field-locker` in `structure-field CanonicalDrazinRegularizationWitness.h_star_canonical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [soft] `law-field-locker` in `structure-field CanonicalDrazinRegularizationWitness.k` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [soft] `law-field-locker` in `structure-field CanonicalDrazinRegularizationWitness.h_drazin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L285 [soft] `law-field-locker` in `structure-field CanonicalDrazinRegularizationWitness.h_star` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L304 [soft] `law-field-locker` in `structure-field DIIITransportCommutatorWitness.hEvenDef` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [soft] `law-field-locker` in `structure-field DIIITransportCommutatorWitness.M` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L308 [soft] `law-field-locker` in `structure-field DIIITransportCommutatorWitness.P0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L312 [soft] `law-field-locker` in `structure-field DIIITransportCommutatorWitness.hA` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field DIIITransportCommutatorWitness.hplus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L316 [soft] `law-field-locker` in `structure-field DIIITransportCommutatorWitness.hminus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field DIIITransportCommutatorWitness.hBoundaryOnZeroModes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L331 [soft] `law-field-locker` in `structure-field DIIITransportCommutatorWitness.hBoundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L358 [advisory] `bridge-shaped-declaration` in `theorem bridge_zpe_gravity` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L358 [advisory] `placeholder-naming` in `theorem bridge_zpe_gravity` — declaration name indicates temporary/external hypothesis surface
  - L376 [advisory] `bridge-shaped-declaration` in `theorem bridge_zpe_gravity_of_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L376 [advisory] `placeholder-naming` in `theorem bridge_zpe_gravity_of_witness` — declaration name indicates temporary/external hypothesis surface
  - L395 [advisory] `bridge-shaped-declaration` in `theorem bridge_zpe_gravity_of_certifiedInverseKernel` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L395 [advisory] `placeholder-naming` in `theorem bridge_zpe_gravity_of_certifiedInverseKernel` — declaration name indicates temporary/external hypothesis surface
  - L420 [advisory] `bridge-shaped-declaration` in `theorem bridge_fluid_helicity` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L420 [advisory] `existential-packaging` in `theorem bridge_fluid_helicity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L420 [advisory] `placeholder-naming` in `theorem bridge_fluid_helicity` — declaration name indicates temporary/external hypothesis surface
  - L439 [advisory] `local-hypothesis-injection` in `theorem bridge_fluid_helicity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L449 [advisory] `bridge-shaped-declaration` in `theorem bridge_fluid_helicity_of_matchedWitness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L449 [advisory] `existential-packaging` in `theorem bridge_fluid_helicity_of_matchedWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L449 [advisory] `placeholder-naming` in `theorem bridge_fluid_helicity_of_matchedWitness` — declaration name indicates temporary/external hypothesis surface
  - L498 [soft] `law-field-locker` in `structure-field FluidHelicityProductionWitness.regularization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L500 [soft] `law-field-locker` in `structure-field FluidHelicityProductionWitness.helicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L512 [soft] `law-field-locker` in `structure-field CanonicalDrazinFluidHelicityWitness.canonicalRegularization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L514 [soft] `law-field-locker` in `structure-field CanonicalDrazinFluidHelicityWitness.helicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L529 [soft] `law-field-locker` in `structure-field CanonicalDrazinFluidHelicityWitness.helicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L545 [advisory] `bridge-shaped-declaration` in `theorem bridge_fluid_helicity_of_regularizationWitness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L545 [advisory] `existential-packaging` in `theorem bridge_fluid_helicity_of_regularizationWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L545 [advisory] `placeholder-naming` in `theorem bridge_fluid_helicity_of_regularizationWitness` — declaration name indicates temporary/external hypothesis surface
  - L566 [advisory] `bridge-shaped-declaration` in `theorem bridge_fluid_helicity_of_productionWitness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L566 [advisory] `existential-packaging` in `theorem bridge_fluid_helicity_of_productionWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L566 [advisory] `placeholder-naming` in `theorem bridge_fluid_helicity_of_productionWitness` — declaration name indicates temporary/external hypothesis surface
  - L583 [advisory] `bridge-shaped-declaration` in `theorem bridge_fluid_helicity_of_canonicalDrazinProductionWitness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L583 [advisory] `existential-packaging` in `theorem bridge_fluid_helicity_of_canonicalDrazinProductionWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L583 [advisory] `placeholder-naming` in `theorem bridge_fluid_helicity_of_canonicalDrazinProductionWitness` — declaration name indicates temporary/external hypothesis surface
  - L604 [advisory] `bridge-shaped-declaration` in `theorem bridge_fluid_helicity_of_regularization` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L604 [advisory] `existential-packaging` in `theorem bridge_fluid_helicity_of_regularization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L604 [advisory] `placeholder-naming` in `theorem bridge_fluid_helicity_of_regularization` — declaration name indicates temporary/external hypothesis surface
  - L627 [advisory] `bridge-shaped-declaration` in `theorem bridge_fluid_helicity_of_regularization_of_finiteDimensional` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L627 [advisory] `existential-packaging` in `theorem bridge_fluid_helicity_of_regularization_of_finiteDimensional` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L627 [advisory] `placeholder-naming` in `theorem bridge_fluid_helicity_of_regularization_of_finiteDimensional` — declaration name indicates temporary/external hypothesis surface
  - L673 [advisory] `bridge-shaped-declaration` in `theorem bridge_thermal_bott_of_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L673 [advisory] `placeholder-naming` in `theorem bridge_thermal_bott_of_witness` — declaration name indicates temporary/external hypothesis surface
  - L690 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L781 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_matchedHelicityWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L841 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_ownerWitnesses` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L902 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_ownerWitnesses_and_thermalBottWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L959 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1068 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1145 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_ownerWitnesses_and_thermalBottWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1219 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1308 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_of_mismatch_forces_projector_noncommute_of_ownerWitnesses` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1391 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1515 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_with_nonzero_scale_and_diii_transportCommutator_of_quasilatticeAnalyticalIndex_of_mismatch_forces_projector_noncommute_of_diiiWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1609 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1691 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_of_matchedHelicityWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1750 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_ownerWitnesses` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1807 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_regularization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1866 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_regularization_of_zpeGravityWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1923 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1989 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2047 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_of_canonicalDrazinRegularizationWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2119 [advisory] `existential-packaging` in `theorem squeezingLogShear_bound_of_capstone_conjunction` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2219 [advisory] `existential-packaging` in `theorem squeezingLogShear_bound_of_bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2343 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_cocycle_sourced` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2593 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_cocycle_sourced_natMatch` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2668 [advisory] `existential-packaging` in `def bits_to_gravity_to_fluid_capstone_cocycle_sourced_natMatch_fluidWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2738 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2813 [advisory] `existential-packaging` in `theorem bits_to_gravity_to_fluid_capstone_tomita_cocycle_sourced_natMatch` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

