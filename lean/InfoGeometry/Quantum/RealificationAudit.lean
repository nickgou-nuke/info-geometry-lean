/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.Realification
import InfoGeometry.Quantum.RealificationStates
import InfoGeometry.Quantum.RealificationChannels
import InfoGeometry.Quantum.RealificationTensor
import InfoGeometry.Quantum.RealKTensor
import InfoGeometry.Quantum.RealificationCategory
import InfoGeometry.Quantum.RealificationCompression

/-!
# Axiom audit for finite real-number quantum theory

This companion checks every public definition and theorem introduced by the
seven implementation owners. Private helpers are included transitively through
the public results that use them. Expected kernel dependencies are limited to
`propext`, `Classical.choice`, and `Quot.sound`; declarations may use a subset
or no axioms. Run this source through Lean to inspect the actual dependency
sets rather than treating successful elaboration alone as an axiom audit.
-/

-- Realification
#print axioms InfoGeometry.Quantum.Realification.realify
#print axioms InfoGeometry.Quantum.Realification.realify_inl_inl
#print axioms InfoGeometry.Quantum.Realification.realify_inl_inr
#print axioms InfoGeometry.Quantum.Realification.realify_inr_inl
#print axioms InfoGeometry.Quantum.Realification.realify_inr_inr
#print axioms InfoGeometry.Quantum.Realification.realify_zero
#print axioms InfoGeometry.Quantum.Realification.realify_add
#print axioms InfoGeometry.Quantum.Realification.realify_neg
#print axioms InfoGeometry.Quantum.Realification.realify_sub
#print axioms InfoGeometry.Quantum.Realification.realify_smul
#print axioms InfoGeometry.Quantum.Realification.realify_conjTranspose
#print axioms InfoGeometry.Quantum.Realification.realify_star
#print axioms InfoGeometry.Quantum.Realification.unrealify
#print axioms InfoGeometry.Quantum.Realification.unrealify_realify
#print axioms InfoGeometry.Quantum.Realification.realify_injective
#print axioms InfoGeometry.Quantum.Realification.realify_mul
#print axioms InfoGeometry.Quantum.Realification.realify_one
#print axioms InfoGeometry.Quantum.Realification.trace_realify
#print axioms InfoGeometry.Quantum.Realification.realifyRingHom
#print axioms InfoGeometry.Quantum.Realification.realifyLinearMap
#print axioms InfoGeometry.Quantum.Realification.realify_sum
#print axioms InfoGeometry.Quantum.Realification.realify_commute_iff
#print axioms InfoGeometry.Quantum.Realification.internalJ
#print axioms InfoGeometry.Quantum.Realification.internalJ_eq_realify
#print axioms InfoGeometry.Quantum.Realification.internalJ_sq
#print axioms InfoGeometry.Quantum.Realification.realify_commutes_internalJ
#print axioms InfoGeometry.Quantum.Realification.realify_unrealify_of_commute
#print axioms InfoGeometry.Quantum.Realification.mem_range_realify_iff_commute

-- RealificationStates
#print axioms InfoGeometry.Quantum.Realification.realifyVector
#print axioms InfoGeometry.Quantum.Realification.unrealifyVector
#print axioms InfoGeometry.Quantum.Realification.realifyVector_unrealifyVector
#print axioms InfoGeometry.Quantum.Realification.unrealifyVector_realifyVector
#print axioms InfoGeometry.Quantum.Realification.realify_mulVec
#print axioms InfoGeometry.Quantum.Realification.dotProduct_realifyVector
#print axioms InfoGeometry.Quantum.Realification.quadratic_realify
#print axioms InfoGeometry.Quantum.Realification.realify_isHermitian_iff
#print axioms InfoGeometry.Quantum.Realification.realify_posSemidef_iff
#print axioms InfoGeometry.Quantum.Realification.state
#print axioms InfoGeometry.Quantum.Realification.state_injective
#print axioms InfoGeometry.Quantum.Realification.state_commutes_internalJ
#print axioms InfoGeometry.Quantum.Realification.state_posSemidef
#print axioms InfoGeometry.Quantum.Realification.trace_state
#print axioms InfoGeometry.Quantum.Realification.trace_state_eq_one
#print axioms InfoGeometry.Quantum.Realification.state_density
#print axioms InfoGeometry.Quantum.Realification.density_preimage
#print axioms InfoGeometry.Quantum.Realification.born_readout
#print axioms InfoGeometry.Quantum.Realification.trace_mul_im_eq_zero
#print axioms InfoGeometry.Quantum.Realification.born_readout_complex
#print axioms InfoGeometry.Quantum.Realification.state_purity
#print axioms InfoGeometry.Quantum.Realification.state_purity_of_idempotent
#print axioms InfoGeometry.Quantum.Realification.state_conjugation

-- RealificationChannels
#print axioms InfoGeometry.Quantum.Realification.realify_povm
#print axioms InfoGeometry.Quantum.Realification.born_readout_sum
#print axioms InfoGeometry.Quantum.Realification.realify_krausChannel
#print axioms InfoGeometry.Quantum.Realification.state_krausChannel
#print axioms InfoGeometry.Quantum.Realification.state_krausMap
#print axioms InfoGeometry.Quantum.Realification.realify_kraus_completeness
#print axioms InfoGeometry.Quantum.Realification.real_krausChannel_posSemidef
#print axioms InfoGeometry.Quantum.Realification.realified_channel_density
#print axioms InfoGeometry.Quantum.Realification.realified_spin_noncommute

-- RealificationTensor
#print axioms InfoGeometry.Quantum.Realification.unrealify_zero
#print axioms InfoGeometry.Quantum.Realification.unrealify_add
#print axioms InfoGeometry.Quantum.Realification.unrealify_smul
#print axioms InfoGeometry.Quantum.Realification.unrealify_one
#print axioms InfoGeometry.Quantum.Realification.alignedTensor
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_eq_realify
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_realify
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_zero_left
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_zero_right
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_add_left
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_add_right
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_smul_left
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_smul_right
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_commutes_internalJ
#print axioms InfoGeometry.Quantum.Realification.unrealify_mul_of_commute
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_mul
#print axioms InfoGeometry.Quantum.Realification.unrealify_conjTranspose_of_commute
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_conjTranspose
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_posSemidef
#print axioms InfoGeometry.Quantum.Realification.state_kronecker
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_conjugation_realify
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_local_left
#print axioms InfoGeometry.Quantum.Realification.alignedTensor_born_product

-- RealKTensor
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.complexTensor
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.obj
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.tmul
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.ofReal_smul
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.I_smul
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.tmul_add_left
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.tmul_add_right
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.tmul_smul_left
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.tmul_smul_right
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.bilinear
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.bilinear_apply
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.K_tmul_left
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.K_tmul_right
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.K_balance
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.hom_ext
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.map
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.map_tmul
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.map_id
#print axioms InfoGeometry.Quantum.RealKCategory.RealKVect.RealKTensor.map_comp

-- RealificationCategory
#print axioms InfoGeometry.Quantum.Realification.doubledRealK
#print axioms InfoGeometry.Quantum.Realification.realify_intertwines_internalJ
#print axioms InfoGeometry.Quantum.Realification.realifiedHom
#print axioms InfoGeometry.Quantum.Realification.realifiedHom_apply
#print axioms InfoGeometry.Quantum.Realification.realifiedHom_one
#print axioms InfoGeometry.Quantum.Realification.realifiedHom_mul
#print axioms InfoGeometry.Quantum.Realification.realifiedHom_realifyVector
#print axioms InfoGeometry.Quantum.Realification.realifyVectorLinear
#print axioms InfoGeometry.Quantum.Realification.unrealifyVectorLinear
#print axioms InfoGeometry.Quantum.Realification.internalJ_realifyVector
#print axioms InfoGeometry.Quantum.Realification.unrealifyVector_internalJ
#print axioms InfoGeometry.Quantum.Realification.coordinateIso
#print axioms InfoGeometry.Quantum.Realification.coordinateIso_naturality

-- RealificationCompression
#print axioms InfoGeometry.Quantum.Realification.internalJ_transpose
#print axioms InfoGeometry.Quantum.Realification.phaseInvolution
#print axioms InfoGeometry.Quantum.Realification.phaseInvolution_transpose
#print axioms InfoGeometry.Quantum.Realification.phaseInvolution_sq
#print axioms InfoGeometry.Quantum.Realification.phaseProjector
#print axioms InfoGeometry.Quantum.Realification.phaseProjector_sq
#print axioms InfoGeometry.Quantum.Realification.phaseProjector_transpose
#print axioms InfoGeometry.Quantum.Realification.phaseProjector_isHermitian
#print axioms InfoGeometry.Quantum.Realification.compressedTensor
#print axioms InfoGeometry.Quantum.Realification.compressedTensor_posSemidef
#print axioms InfoGeometry.Quantum.Realification.compressedTensor_add_left
#print axioms InfoGeometry.Quantum.Realification.compressedTensor_add_right
#print axioms InfoGeometry.Quantum.Realification.compressedTensor_smul_left
#print axioms InfoGeometry.Quantum.Realification.compressedTensor_smul_right
