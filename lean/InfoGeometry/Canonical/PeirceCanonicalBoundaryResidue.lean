import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PeircePositiveBoundary

namespace InfoGeometry.Canonical

def peirceBoundaryCoordinatePath
    (b : PeirceBoundaryCoordinate) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  match b with
  | .a00 => ![![t, 1], ![1, 1]]
  | .a01 => ![![1, t], ![1, 1]]
  | .a10 => ![![1, 1], ![t, 1]]
  | .a11 => ![![1, 1], ![1, t]]

theorem peirceBoundaryCoordinatePath_value
    (b : PeirceBoundaryCoordinate) (t : ℝ) :
    peirceBoundaryValue b (peirceBoundaryCoordinatePath b t) = t := by
  fin_cases b <;> rfl

theorem peirceBoundaryCoordinatePath_injective
    (b : PeirceBoundaryCoordinate) :
    Function.Injective (peirceBoundaryCoordinatePath b) := by
  intro s t hst
  have hvalue := congrArg (peirceBoundaryValue b) hst
  simpa [peirceBoundaryCoordinatePath_value] using hvalue

end InfoGeometry.Canonical
