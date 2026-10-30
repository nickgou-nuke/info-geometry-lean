/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.AttentionFrameCorrections
import InfoGeometry.LLM.AttentionFrameWhitening
import InfoGeometry.LLM.AttentionOccupationRefinement

open InfoGeometry.LLM.AttentionFrameCorrections
open InfoGeometry.LLM.AttentionFrameWhitening
open InfoGeometry.LLM.AttentionOccupationRefinement

#print axioms distinct_head_occupation_projections_overlap
#print axioms occupation_projections_not_complete
#print axioms occupation_projection_not_central
#print axioms keys_not_orthogonal
#print axioms nonorthogonal_key_readouts_not_normalized
#print axioms key_readout_not_softmax
#print axioms whitening_frame_whitening
#print axioms effect_posSemidef
#print axioms sum_effect
#print axioms readout_probability
#print axioms joint_sector_idempotent
#print axioms joint_sectors_disjoint
#print axioms joint_sectors_complete
