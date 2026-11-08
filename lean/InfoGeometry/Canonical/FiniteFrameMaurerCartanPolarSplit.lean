import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite frame Maurer--Cartan product split

This file owns the purely algebraic finite-matrix identity behind the
phase/volume separation of an invertible complex frame.

No differential-form, polar-decomposition, or winding structure is assumed
here.  The inputs `dU` and `dP` are arbitrary tangent matrices, and the tangent
of the product frame is represented by the Leibniz expression
`dU * P + U * dP`.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteFrameMaurerCartanPolarSplit

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ
local notation "Frame" => Matrix.GeneralLinearGroup n ℂ

/-- Left logarithmic derivative `G⁻¹ dG` of an invertible finite frame. -/
def leftMaurerCartan (G : Frame) (dG : Mat) : Mat :=
  (↑(G⁻¹) : Mat) * dG

/-- Leibniz tangent of the product frame `U * P`. -/
def productTangent (U P : Frame) (dU dP : Mat) : Mat :=
  dU * (P : Mat) + (U : Mat) * dP

/--
The left logarithmic derivative of a product splits into a conjugated
left logarithmic derivative of the first factor and the left logarithmic
derivative of the second factor.
-/
theorem leftMaurerCartan_mul
    (U P : Frame) (dU dP : Mat) :
    leftMaurerCartan (U * P) (productTangent U P dU dP) =
      (↑(P⁻¹) : Mat) * leftMaurerCartan U dU * (P : Mat) +
        leftMaurerCartan P dP := by
  simp [leftMaurerCartan, productTangent, mul_add, mul_assoc]

/--
After matrix trace, the conjugation in the product formula disappears.
This is the finite noncommutative logarithmic-Jacobian product rule.
-/
theorem trace_leftMaurerCartan_mul
    (U P : Frame) (dU dP : Mat) :
    Matrix.trace
        (leftMaurerCartan (U * P) (productTangent U P dU dP)) =
      Matrix.trace (leftMaurerCartan U dU) +
        Matrix.trace (leftMaurerCartan P dP) := by
  rw [leftMaurerCartan_mul, Matrix.trace_add]
  congr 1
  calc
    Matrix.trace
        ((↑(P⁻¹) : Mat) * leftMaurerCartan U dU * (P : Mat)) =
        Matrix.trace
          ((P : Mat) * ((↑(P⁻¹) : Mat) * leftMaurerCartan U dU)) := by
            exact Matrix.trace_mul_comm
              ((↑(P⁻¹) : Mat) * leftMaurerCartan U dU) (P : Mat)
    _ = Matrix.trace (leftMaurerCartan U dU) := by
      simp

end InfoGeometry.Canonical.FiniteFrameMaurerCartanPolarSplit
