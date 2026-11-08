/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionStageColimitState

/-!
# Kernel axiom audit for the finite attention state colimit bridge

This companion prints the axiom dependencies of the owner declarations. It
does not package theorem propositions into a certificate structure.
-/

open InfoGeometry.QuantumContext.AttentionStageColimitState

#print axioms attentionStageDensity_eq_scaled_complexification
#print axioms attentionStageDensity_apply
#print axioms attentionStageDensity_normalizedTrace
#print axioms attentionStageDensity_hermitian
#print axioms attentionStageDensity_positive
#print axioms attentionColimitFunctional_unital
#print axioms attentionColimitFunctional_starSquare_nonneg
#print axioms attentionColimitFunctional_starSquare_im_zero
#print axioms attentionColimitFunctional_seed_readout
#print axioms attentionColimitFunctional_real_seed_readout
