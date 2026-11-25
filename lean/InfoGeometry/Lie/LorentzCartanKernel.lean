/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Longitudinal kernel of the real Lorentz Poisson coordinate matrix

Coordinates are `(J₁,J₂,J₃,K₁,K₂,K₃)`. The explicit skew matrix below is
the convention of the supplied Lorentz Lie–Poisson calculation. This module
proves matrix identities and a coordinate dual pairing. Kernel membership
does not imply that the dual pairing is zero.
-/

noncomputable section

namespace InfoGeometry.Lie.LorentzCartanKernel

open Matrix

/-- The six-coordinate real Lorentz Poisson matrix, with rotation coordinates first. -/
def lorentzPoissonMat (J₁ J₂ J₃ K₁ K₂ K₃ : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![  0, -J₃,  J₂,   0, -K₃,  K₂;
      J₃,   0, -J₁,  K₃,   0, -K₁;
     -J₂,  J₁,   0, -K₂,  K₁,   0;
       0, -K₃,  K₂,   0,  J₃, -J₂;
      K₃,   0, -K₁, -J₃,   0,  J₁;
     -K₂,  K₁,   0,  J₂, -J₁,   0]

/-- A vector in the longitudinal rotation/boost coordinate plane. -/
def loxodromicTempVec (a b : ℝ) : Fin 6 → ℝ := ![0, 0, b, 0, 0, a]

/-- Coordinate charge embedding; the physical interpretation of `E` is external. -/
def modeCharge (E m : ℝ) : Fin 6 → ℝ := ![0, 0, m, 0, 0, E]

/-- The real coordinate covector producing the co-rotating exponent. -/
def rotatingTemperature (β Ω : ℝ) : Fin 6 → ℝ :=
  loxodromicTempVec β (-β * Ω)

theorem lorentzPoissonMat_transpose (J₁ J₂ J₃ K₁ K₂ K₃ : ℝ) :
    (lorentzPoissonMat J₁ J₂ J₃ K₁ K₂ K₃)ᵀ =
      -lorentzPoissonMat J₁ J₂ J₃ K₁ K₂ K₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lorentzPoissonMat]

/-- Every longitudinal temperature lies in the kernel at a longitudinal state. -/
theorem longitudinal_temperature_mem_kernel (J₃ K₃ a b : ℝ) :
    (lorentzPoissonMat 0 0 J₃ 0 0 K₃).mulVec (loxodromicTempVec a b) = 0 := by
  ext i
  fin_cases i <;>
    simp [lorentzPoissonMat, loxodromicTempVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem rotatingTemperature_mem_kernel (β Ω E m : ℝ) :
    (lorentzPoissonMat 0 0 m 0 0 E).mulVec (rotatingTemperature β Ω) = 0 :=
  longitudinal_temperature_mem_kernel m E β (-β * Ω)

/-- The coordinate pairing is exactly the co-rotating Gibbs exponent. -/
theorem modeCharge_dot_rotatingTemperature (β Ω E m : ℝ) :
    dotProduct (modeCharge E m) (rotatingTemperature β Ω) = β * (E - Ω * m) := by
  simp [modeCharge, rotatingTemperature, loxodromicTempVec, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- A nonzero pairing can coexist with Poisson kernel membership. -/
theorem kernel_pairing_counterexample :
    (lorentzPoissonMat 0 0 0 0 0 1).mulVec (rotatingTemperature 1 0) = 0 ∧
      dotProduct (modeCharge 1 0) (rotatingTemperature 1 0) = 1 := by
  constructor
  · exact rotatingTemperature_mem_kernel 1 0 1 0
  · rw [modeCharge_dot_rotatingTemperature]
    norm_num

end InfoGeometry.Lie.LorentzCartanKernel
