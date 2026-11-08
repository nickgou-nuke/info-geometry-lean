/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.GenericGradedJacobiClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalExtremeActionData
import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

/-!
# Freudenthal 6-Lane Homogeneous Jacobi Projectors and Reduction

This module connects the generic graded Jacobi decomposition to the 5-graded Freudenthal carrier
`FiveGradedCarrier D = ℝ ⊕ F ⊕ 𝔤₀^symp ⊕ ℝ ⊕ F ⊕ ℝ`.

## Mathematical Structure:
1. `JacobiLane`: The 6 atomic lanes `minus2, minus1, zeroSymp, zeroScale, plus1, plus2`.
2. `lanePart D g`: Projector for each lane.
3. `sum_lanePart`: Exact identity: the sum of the 6 lane projections equals the full element.
4. Homogeneous cell reduction:
   The global 5-graded Jacobi identity reduces to the $6^3 = 216$ atomic lane cells.

The decomposition is algebraic and does not assert global Jacobi for the legacy
bracket. The constructive Lie algebra on this carrier is installed in
`FreudenthalSymplecticContactLieAlgebra`.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The six atomic grading lanes for the Freudenthal carrier. -/
inductive JacobiLane
  | minus2
  | minus1
  | zeroSymp
  | zeroScale
  | plus1
  | plus2
  deriving DecidableEq

/-- Projector onto each atomic grading lane. -/
def lanePart (lane : JacobiLane) (x : FiveGradedCarrier D) : FiveGradedCarrier D :=
  match lane with
  | JacobiLane.minus2    => ⟨x.minus2, 0, 0, 0, 0, 0⟩
  | JacobiLane.minus1    => ⟨0, x.minus1, 0, 0, 0, 0⟩
  | JacobiLane.zeroSymp  => ⟨0, 0, x.zero_symp, 0, 0, 0⟩
  | JacobiLane.zeroScale => ⟨0, 0, 0, x.zero_scale, 0, 0⟩
  | JacobiLane.plus1     => ⟨0, 0, 0, 0, x.plus1, 0⟩
  | JacobiLane.plus2     => ⟨0, 0, 0, 0, 0, x.plus2⟩

/-- 🏆 Reconstruction Theorem: Sum of all 6 lane projectors is the identity. -/
theorem sum_lanePart (x : FiveGradedCarrier D) :
    lanePart D .minus2 x + lanePart D .minus1 x + lanePart D .zeroSymp x +
    lanePart D .zeroScale x + lanePart D .plus1 x + lanePart D .plus2 x = x := by
  apply FiveGradedCarrier.ext <;>
    dsimp [lanePart, FiveGradedCarrier.instAdd] <;>
    simp


end InfoGeometry.Exceptional.Freudenthal
