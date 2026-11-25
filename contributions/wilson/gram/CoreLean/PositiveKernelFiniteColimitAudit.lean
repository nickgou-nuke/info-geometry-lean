/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import CoreLean.PositiveKernelFiniteColimit
public import CoreLean.PositiveKernelLimit

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-!
The assumptions displayed here should consist only of Lean's standard logical
foundations (`propext`, `Classical.choice`, `Quot.sound`). Kernel positivity and cutoff
convergence are explicit theorem parameters; neither is introduced as a new axiom.
-/

#print axioms CoreLean.PositiveKernel.inner_preToHilbert
#print axioms CoreLean.PositiveKernel.inner_feature
#print axioms CoreLean.PositiveKernel.inner_finiteEval
#print axioms CoreLean.PositiveKernel.mem_ker_finiteEval_iff
#print axioms CoreLean.PositiveKernel.mem_ker_finiteEval_iff_radical
#print axioms CoreLean.PositiveKernel.quotientEmbedding_injective
#print axioms CoreLean.PositiveKernel.quotientEmbedding_mk
#print axioms CoreLean.PositiveKernel.inner_quotientEmbedding_mk
#print axioms CoreLean.PositiveKernel.finiteEval_zeroExtend
#print axioms CoreLean.PositiveKernel.finiteGram_zeroExtend
#print axioms CoreLean.PositiveKernel.stage_mono
#print axioms CoreLean.PositiveKernel.stageMap_self
#print axioms CoreLean.PositiveKernel.stageMap_comp
#print axioms CoreLean.PositiveKernel.quotientEmbedding_quotientMap
#print axioms CoreLean.PositiveKernel.quotientMap_mk
#print axioms CoreLean.PositiveKernel.quotientMap_injective
#print axioms CoreLean.PositiveKernel.colimitToHilbert_stage
#print axioms CoreLean.PositiveKernel.colimitToHilbert_injective
#print axioms CoreLean.PositiveKernel.existsUnique_lift
#print axioms CoreLean.PositiveKernel.feature_mem_range_colimit
#print axioms CoreLean.PositiveKernel.preToHilbert_mem_range_colimit
#print axioms CoreLean.PositiveKernel.denseRange_colimitToHilbert
#print axioms CoreLean.PositiveKernel.range_colimitToHilbert_eq_union
#print axioms CoreLean.PositiveKernel.dense_stageUnion
#print axioms CoreLean.PositiveKernel.completionToHilbert_surjective
#print axioms CoreLean.PositiveKernel.completionEquiv_stage
#print axioms CoreLean.PositiveKernel.posSemidef_of_tendsto
#print axioms CoreLean.PositiveKernel.stageToColimitIsometry
#print axioms CoreLean.PositiveKernel.completionEquiv
