import InfoGeometry.Epistemology.IsometricCutState
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Epistemology.HolographicTensorNetwork

/-!
# Audit Companion: Holographic Tensor Networks

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Epistemology.HolographicTensorNetwork`.
-/

open InfoGeometry.Epistemology.HolographicTensorNetwork

#print axioms min_cut_le_cut
#print axioms rtDeficit_nonneg
#print axioms flat_entropy_eq_capacity
#print axioms mera_entropy_bound
#print axioms code_projector_idempotent
#print axioms code_projector_annihilates_complement
#print axioms happy_deficit_zero
#print axioms exact_rt_saturation_iff
#print axioms operator_reconstruction_fidelity
#print axioms compile_holographic_tensor_network

-- Finite isometric-state prerequisites; these do not certify network saturation.
#print axioms InfoGeometry.Epistemology.IsometricCutState.cutDensity_posSemidef
#print axioms InfoGeometry.Epistemology.IsometricCutState.cutDensity_trace
#print axioms InfoGeometry.Epistemology.IsometricCutState.cutDensity_sq
#print axioms InfoGeometry.Epistemology.IsometricCutState.cutDensity_mul_encoding
#print axioms InfoGeometry.Epistemology.IsometricCutState.encoding_injective
#print axioms InfoGeometry.Epistemology.IsometricCutState.cutProjection_rank
#print axioms InfoGeometry.Epistemology.IsometricCutState.uniformCutWeight_entropy
#print axioms InfoGeometry.Epistemology.IsometricCutState.uniformCutWeight_entropy_capacity
