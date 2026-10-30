/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.GromovPermutationNormalization

/-!
# Kernel axiom audit for secondary-normalization counterexamples

The unweighted additivity claim is false. Mass weighted pooling is the
owner-aligned replacement, with its zero-mass condition explicit.
-/

#print axioms InfoGeometry.Probability.GromovPermutationNormalization.normalization_non_additive_counterexample
#print axioms InfoGeometry.Probability.GromovPermutationNormalization.normalization_sum_eq_mass_mixture
#print axioms InfoGeometry.Probability.GromovPermutationNormalization.mass_mixture_weights_probability
#print axioms InfoGeometry.Probability.GromovPermutationNormalization.normalization_pooled_nonnegative_weights
