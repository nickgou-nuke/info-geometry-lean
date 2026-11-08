/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.NormalizedDiracSelfAdjoint
import InfoGeometry.Canonical.PeirceSquareZeroExamples

namespace InfoGeometry.Core.NormalizedDiracSelfAdjoint
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Canonical.PeirceSquareZeroExamples

example : ¬ IsSelfAdjoint (normalizedDirac scaledStep reciprocalStep) := by
  rw [normalizedDirac_isSelfAdjoint_iff reciprocalStep_mp scaledStep_square_zero]
  exact reciprocalStep_ne_star_scaledStep

example : IsMoorePenroseInverse (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 := by
  simp [IsMoorePenroseInverse]

example : IsSelfAdjoint (normalizedDirac (0 : Matrix (Fin 2) (Fin 2) ℝ) 0) := by
  change star (0 + 0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 + 0
  simp

abbrev forwardWitness : Matrix (Fin 2) (Fin 2) ℝ := scaledStep
noncomputable abbrev reverseWitness : Matrix (Fin 2) (Fin 2) ℝ := reciprocalStep

theorem scaled_pair_noncommuting :
    forwardWitness * reverseWitness ≠ reverseWitness * forwardWitness := by
  change scaledStep * reciprocalStep ≠ reciprocalStep * scaledStep
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [scaledStep, reciprocalStep, Matrix.mul_apply, Fin.sum_univ_two] at he

#print axioms normalizedDirac_isSelfAdjoint_iff
#print axioms normalizedDirac_eq_metric_iff
#print axioms reciprocal_sum_not_selfAdjoint
#print axioms scaled_pair_noncommuting

end InfoGeometry.Core.NormalizedDiracSelfAdjoint
