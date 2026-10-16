/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.PolarizedAttentionMarkovDrazin

/-!
# Kernel axiom audit for polarized-attention Markov specialization

The checked declarations specialize existing finite Markov results to the
repository's actual polarized Gibbs-row attention matrix.
-/

#print axioms
  InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention.existsUnique_positive_normalized_stationary_row

#print axioms
  InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention.range_laplacian_eq_weightedMean_ker

#print axioms
  InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention.poisson_solution_of_weightedMean_zero

#print axioms
  InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention.principalProjector_apply_eq_weightedMean
