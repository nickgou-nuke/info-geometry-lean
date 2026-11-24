# Independent fresh-axiom evidence from CI6

Artifact 14916487441 from run45385261804, job138414407353, remote source21816519e42b9f76a0c8004650c6b11a6024774f.

The ZIP was downloaded through the GitHub artifact tool. Its SHA-256 was independently checked against the Actions artifact digest: `e5cf4cfe9ac3812b57bc21fe148be32dadb6a074a09229a506810bd541fa87fa`.

The body below is the exact UTF-8 content of `triality-cotangent-axioms.log`; no timestamp stripping, rewriting, or synthesized records were used. Raw log SHA-256: `bb5a2be5a44178a5216cd9fb53e9a32ddbdf446c600e5a0c0e8297a6e8f1c084`.

Independent command: `python3 verification/triality-cotangent/audit.py --log /dev/stdin`, with this actual artifact log supplied on stdin. Exit: 0.

```text
Source coverage: 202 public declarations in 7 owners
Lean axiom audit passed; foundational axioms: ['Classical.choice', 'Quot.sound', 'propext']
```

## Actual raw fresh invocation log

```text
[triality-cotangent] requesting shared build lock
[triality-cotangent] acquired shared build lock
[triality-cotangent] input snapshot {"files": 53, "sha256": "be56d8ec0eec0d8f3fcb2520cf95ca6459e5fbd5d1039f9e6039b0da335cc75d"}
[triality-cotangent] runtime {"lake": "/home/runner/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake", "lake_sha256": "6f53827dab18010d6c690d14c8401cacabc1db958edb3552a877ed4cf1dd995d", "lake_version": "Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)", "lean": "/home/runner/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean", "lean_sha256": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550", "lean_version": "Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)", "requested_lake": "/home/runner/.elan/bin/lake", "toolchain": "leanprover/lean4:v4.34.1"}
[triality-cotangent] /home/runner/.elan/bin/lake -d /home/runner/work/info-geometry-lean/info-geometry-lean/verification/triality-cotangent env lean lean/InfoGeometry/Geometry/TrialityCotangentAudit.lean
'InfoGeometry.Geometry.CotangentActionGroupoid.coadj' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.coadj_apply' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.coadj_one' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.coadj_mul' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.coadj_inv_coadj' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.coadj_coadj_inv' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.coadjointAction' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.CotangentGroupoid' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.cotangentGroupoid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.Arrow' does not depend on any axioms
'InfoGeometry.Geometry.CotangentActionGroupoid.source' does not depend on any axioms
'InfoGeometry.Geometry.CotangentActionGroupoid.target' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.unit' depends on axioms: [propext]
'InfoGeometry.Geometry.CotangentActionGroupoid.inverse' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.Composable' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.comp' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.source_unit' depends on axioms: [propext]
'InfoGeometry.Geometry.CotangentActionGroupoid.target_unit' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.source_inverse' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.target_inverse' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.inverse_inverse' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.source_comp' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.target_comp' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.unit_comp' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.comp_unit' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.inverse_comp' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.comp_inverse' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.comp_assoc' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.object' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.toHom' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fromHom' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.target_fromHom' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fromHom_toHom' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.toHom_comp_label' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fromHom_comp' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.coadj_intertwine' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.lift' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.lift_fixed_iff' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.source_lift' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.target_lift' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.composable_lift' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.lift_unit' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.lift_inverse' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.lift_comp' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.liftFunctor' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.liftFunctor_faithful' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.liftFunctor_full' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.liftFunctor_essSurj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.liftFunctor_isEquivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.liftEquivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixed_endpoints' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixed_unit' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixed_inverse' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixed_comp' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedSubgroup' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedDual' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedAction' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.FixedGroupoid' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedGroupoid' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedInclusion' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedInclusion_obj_injective' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedInclusion_faithful' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedInclusion_arrow_fixed' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentActionGroupoid.fixedInclusion_hom_range_iff' depends on axioms: [propext, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentLift_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentLift_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentLift_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.bracketForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.bracketForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentForm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentForm_isAlt' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentForm_skew' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentForm_nondegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentForm_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentLieForm.cotangentForm_lieEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.cardInvertible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.averagingProjection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.averagingProjection_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.averagingProjection_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.averagingProjection_action' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.invariantDual_action' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.invariantDual_average' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.extendInvariantDual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.invariantDualEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.invariantDualEquiv_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.invariantDualEquiv_symm_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedPhaseInclusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedCotangentEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedCotangentEquiv_omega' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedCotangentForm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedCotangentForm_isAlt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedCotangentForm_nondegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedCotangentLieForm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedCotangentLieForm_isAlt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.FiniteCotangentInvariants.fixedCotangentLieForm_nondegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.shear' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.shear_fixed_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.dual_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.shear_dual_fixed_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixedPrimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixedDual' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixed_pairing_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixedPrimalEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixedDualEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixed_phase_finrank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixedPhaseInclusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixedOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixedOmega_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixedOmega_not_nondegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Geometry.CotangentFixedShear.fixed_dual_restriction_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.trialitySwapVS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.trialitySwapSpin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.trialityCycle3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.cartan_s3_triality_presentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.triality_mat4_noncommutative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.s3FixedCartanSubmodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.cartan_s3_fixed_subspace_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.s3FixedCartanEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis.finrank_s3FixedCartanSubmodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTriality.conjugationReflection' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cyclicTriality' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.coordinateChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.coordinateChange_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.coordinateChange_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.coordinateChange_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.coordinateChange_conj_hadamard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTriality.coordinateChange_conj_reflection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTriality.coordinateChange_conj_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.conjugationReflection_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cyclicTriality_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cyclicTriality_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cyclicTriality_sq_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cyclicTriality_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.reflection_conj_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.hadamard_reflection_noncommutative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTriality.hadamard_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.reflection_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cycle_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.fixedCartan' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.mem_fixedCartan_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.fixedCartanEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.finrank_fixedCartan' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.fixedCartanBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.fixedCartanBasis_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.fixedCartanBasis_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.coordinateChange_mem_fixedCartan_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTriality.vectorWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.spinorWeightMinus' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.spinorWeightPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cycle_vectorWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cycle_spinorWeightMinus' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.cycle_spinorWeightPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.weight_orbit_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.weight_orbit_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralMatrix_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralMatrixHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralMatrixHom_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralLinearAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralLinearAction_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralLinearAction_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTriality.labelCycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.labelReflection' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralPermutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralPermutationHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralPermutationHom_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralPermutationHom_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralPermutationEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.s3LinearAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.s3LinearAction_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralMatrix_rotation' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralMatrix_reflection' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.dihedralMatrix_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.fixed_by_dihedral_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTriality.fixed_by_s3_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.cartanRepresentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.cartanRepresentation_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.cartanRepresentation_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.contragredient_eq_dual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.CartanVectorGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.vectorAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.vectorGroupAuto' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.vectorGroupAuto_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.vectorAdjoint_intertwine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.vectorCotangentEquivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.vector_target_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.vector_comp_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.fixed_vector_arrows_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.phaseAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.phaseAction_preserves_omega' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.fixed_phase_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.invariantCartanEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.invariantCartanDualEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.fixedCartanCotangentEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.fixedCartanCotangentEquiv_omega' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.finrank_cartan_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.finrank_cartan_dual_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.finrank_fixed_cartan_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.fixed_cartan_phase_nondegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InfoGeometry.Lie.CartanTrialityCotangent.fixed_cartan_phase_isAlt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[triality-cotangent] Lake exited with code 0
[triality-cotangent] source/configuration/runtime stability passed
[triality-cotangent] released shared build lock
```
