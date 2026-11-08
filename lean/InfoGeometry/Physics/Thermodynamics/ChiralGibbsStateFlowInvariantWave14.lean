/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.Thermodynamics.ChiralGrandCanonicalFiniteKMS

namespace InfoGeometry.Physics.Thermodynamics

open InfoGeometry.Physics
open Matrix

noncomputable section

/-- The finite chiral Gibbs state is invariant under every member of the
diagonal similarity family, independently of the state parameter. -/
theorem chiralGibbsState_similarity_invariant (μ ν : ℝ) (X : BdGBlock ℝ) :
    chiralGibbsState μ (chiralSimilarityFlow ν X) =
      chiralGibbsState μ X := by
  unfold chiralGibbsState chiralGibbsDensity chiralSimilarityFlow
  dsimp [chiralGibbsPartition]
  simp only [smul_mul_assoc, Matrix.trace_smul]
  congr 1
  calc
    Matrix.trace
        (gibbsFactor μ *
          (gibbsFactor ν * X * gibbsFactor (-ν))) =
        Matrix.trace
          (gibbsFactor (-ν) * (gibbsFactor μ * gibbsFactor ν * X)) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm
              (gibbsFactor μ * gibbsFactor ν * X) (gibbsFactor (-ν))
    _ = Matrix.trace (gibbsFactor μ * X) := by
      have hcomm : gibbsFactor (-ν) * gibbsFactor μ =
          gibbsFactor μ * gibbsFactor (-ν) := by
        rw [← gibbsFactor_add, ← gibbsFactor_add]
        congr 1
        ring
      rw [show gibbsFactor (-ν) * (gibbsFactor μ * gibbsFactor ν * X) =
          (gibbsFactor (-ν) * gibbsFactor μ) *
            (gibbsFactor ν * X) by simp only [Matrix.mul_assoc]]
      rw [hcomm]
      congr 1
      calc
        gibbsFactor μ * gibbsFactor (-ν) * (gibbsFactor ν * X) =
            gibbsFactor μ * (gibbsFactor (-ν) * gibbsFactor ν) * X := by
              simp only [Matrix.mul_assoc]
        _ = gibbsFactor μ * X := by
              rw [gibbsFactor_neg_mul]
              simp

end

end InfoGeometry.Physics.Thermodynamics
