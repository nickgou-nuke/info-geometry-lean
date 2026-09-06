import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace VarlamovSoldering

open Matrix

/-- The soldering forms (Pauli matrices) mapping the tangent space to the spin bundle. -/
def sigma_0 : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, 1]]
def sigma_1 : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 1], ![1, 0]]
def sigma_2 : Matrix (Fin 2) (Fin 2) ℂ := ![![0, -Complex.I], ![Complex.I, 0]]
def sigma_3 : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, -1]]

/-- 
The soldering map: takes a 4-vector (t, x, y, z) and solders it into a 2x2 complex matrix (biquaternion).
This is the core of the Cl(1,1) modular atom operation.
-/
def solder (t x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  t • sigma_0 + x • sigma_1 + y • sigma_2 + z • sigma_3

theorem soldering_metric (t x y z : ℂ) :
    Matrix.det (solder t x y z) = t^2 - x^2 - y^2 - z^2 := by
  dsimp [solder, sigma_0, sigma_1, sigma_2, sigma_3]
  simp [Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

end VarlamovSoldering
