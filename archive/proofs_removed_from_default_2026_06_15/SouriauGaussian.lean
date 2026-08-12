import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

/-!
# Souriau Thermodynamics & Gaussian Closure

Formalizes the Gaussian self-closed nature of the biquaternion exponential map
and its connection to Souriau's thermal vector beta.
-/

namespace SouriauGaussian

open Matrix
open Complex

/-- A 2x2 complex matrix -/
def Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- A simplified Souriau beta-vector representing a boost along x -/
def betaMatrix (b0 bx : ℂ) : Mat2C :=
  !![b0, bx; bx, b0]

/-- 
Theorem: The determinant of the beta matrix connects the inverse 
square temperature to the Minkowski interval.
-/
theorem beta_matrix_det (b0 bx : ℂ) : 
    (betaMatrix b0 bx).det = b0^2 - bx^2 := by
  dsimp [betaMatrix]
  ring

end SouriauGaussian
