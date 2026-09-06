import InfoGeometry.Optics.OperatorCausalSoldering

/-!
# Integrated operator-valued causal framework

This module is the algebraic integration boundary for the operator lift.  The
coordinate ring, matrix reconstruction, and doubled-carrier action remain
owned by their existing modules.  Here we expose the already existing
commutator, two-slot curvature, torsion, and cyclic-sum channels after that
reconstruction.  No second curvature or matrix multiplication is introduced.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorCausalFramework

open InfoGeometry.Clifford
open InfoGeometry.Canonical.CoordinateFreeConnectionChannels
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Optics.OperatorLiftCarrier

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW (W : Type*) [AddCommGroup W] [Module ℂ W] := Module.End ℂ W
abbrev Coordinates (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  CausalOperatorCoordinates (EndW W)
abbrev MatrixOperator (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  OperatorMatrix (R := ℂ) (W := W)

/-! ## Algebraic channel readouts -/

theorem matrix_commutator
    (A C : Coordinates W) :
    reconstruct_causal (commutator A C) =
      commutator (reconstruct_causal A) (reconstruct_causal C) := by
  exact reconstruct_causal_commutator A C

theorem action_commutator
    (A C : Coordinates W) :
    matrixAction (reconstruct_causal (commutator A C)) =
      matrixAction (commutator (reconstruct_causal A) (reconstruct_causal C)) := by
  rw [matrix_commutator]

theorem matrix_twoSlotCurvature
    (dAC dCA A C : Coordinates W) :
    reconstruct_causal (twoSlotCurvature dAC dCA A C) =
      twoSlotCurvature
        (reconstruct_causal dAC) (reconstruct_causal dCA)
        (reconstruct_causal A) (reconstruct_causal C) := by
  exact reconstruct_causal_twoSlotCurvature dAC dCA A C

theorem action_twoSlotCurvature
    (dAC dCA A C : Coordinates W) :
    matrixAction (reconstruct_causal (twoSlotCurvature dAC dCA A C)) =
      matrixAction (twoSlotCurvature
        (reconstruct_causal dAC) (reconstruct_causal dCA)
        (reconstruct_causal A) (reconstruct_causal C)) := by
  rw [matrix_twoSlotCurvature]

theorem matrix_twoSlotTorsionLeft
    (dEAC dECA OA EC OC EA : Coordinates W) :
    reconstruct_causal (twoSlotTorsionLeft dEAC dECA OA EC OC EA) =
      twoSlotTorsionLeft
        (reconstruct_causal dEAC) (reconstruct_causal dECA)
        (reconstruct_causal OA) (reconstruct_causal EC)
        (reconstruct_causal OC) (reconstruct_causal EA) := by
  exact reconstruct_causal_twoSlotTorsionLeft dEAC dECA OA EC OC EA

theorem matrix_cyclicSum_of_zero
    (X Y Z : Coordinates W)
    (h : cyclicSum X Y Z = 0) :
    cyclicSum (reconstruct_causal X) (reconstruct_causal Y)
      (reconstruct_causal Z) = 0 := by
  exact reconstruct_causal_cyclicSum_of_zero X Y Z h

/-! ## Faithful action readouts -/

theorem action_twoSlotTorsionLeft
    (dEAC dECA OA EC OC EA : Coordinates W) :
    matrixAction (reconstruct_causal (twoSlotTorsionLeft dEAC dECA OA EC OC EA)) =
      matrixAction (twoSlotTorsionLeft
        (reconstruct_causal dEAC) (reconstruct_causal dECA)
        (reconstruct_causal OA) (reconstruct_causal EC)
        (reconstruct_causal OC) (reconstruct_causal EA)) := by
  rw [matrix_twoSlotTorsionLeft]

theorem action_cyclicSum_of_zero
    (X Y Z : Coordinates W)
    (h : cyclicSum X Y Z = 0) :
    matrixAction (cyclicSum (reconstruct_causal X) (reconstruct_causal Y)
      (reconstruct_causal Z)) = 0 := by
  rw [matrix_cyclicSum_of_zero X Y Z h]
  apply LinearMap.ext
  intro ψ
  exact matrixAction_zero ψ

end InfoGeometry.Optics.OperatorCausalFramework
