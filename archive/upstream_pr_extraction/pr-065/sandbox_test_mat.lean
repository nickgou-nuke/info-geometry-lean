import Mathlib
import InfoGeometry.Lie.SplitOctonionCircularAxialGrading

open InfoGeometry.Lie.SplitOctonionCircularAxialGrading

theorem test (j : Fin 8) (X : Coord) (i : Fin 8) :
  (Pi.basisFun ℝ (Fin 8)).repr X i = X i := by
  rfl
