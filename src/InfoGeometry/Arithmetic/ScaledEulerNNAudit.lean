/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.ScaledEulerNN

open InfoGeometry.Arithmetic.SelfConcordantZetaBarrierProofs

example : NNBoundSq ((9 / 8 : ℝ) * (1 ^ 2 * (1 / 2) / (1 - 1 / 2) ^ 2))
    ((9 / 8 : ℝ) * (-(1 ^ 3 * (1 / 2) * (1 + 1 / 2)) / (1 - 1 / 2) ^ 3)) := by
  norm_num [NNBoundSq]

example : ¬ NNBoundSq (1 ^ 2 * (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2)
    (-(1 ^ 3 * (1 / 2 : ℝ) * (1 + 1 / 2)) / (1 - 1 / 2) ^ 3) := by
  norm_num [NNBoundSq]

#print axioms scaledEuler_NN_iff
#print axioms eulerThreshold_antitone
#print axioms scaledEuler_NN_on_cutoff
#print axioms scaledEuler_NN_cutoff_iff
#print axioms logEulerMode_NN_core_fails
#print axioms logEulerMode_NN_cleared_derivative_bound_fails
