import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Clifford.DiracPauliGamma
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.EmergentSpinorElectromagnetism

This module gives concrete coordinate expansions of selected Dirac-spinor
bilinears.  It does not prove nonvanishing for generic spinors, construct
gravity or electromagnetism, or solve a gauge-generation problem.
-/

namespace InfoGeometry.Canonical.EmergentSpinorElectromagnetism

open Matrix
open Complex
open InfoGeometry.Clifford.DiracPauliGamma

/-- 
Dirac adjoint spinor $\bar{\Psi} = \Psi^\dagger \gamma_0$.
We define it as a row vector. 
-/
def diracAdjoint (Psi : DiracSpinor) : Fin 4 → ℂ :=
  fun j => (star Psi 0) * gamma0 0 j + 
           (star Psi 1) * gamma0 1 j + 
           (star Psi 2) * gamma0 2 j + 
           (star Psi 3) * gamma0 3 j

/--
The inner product representing $\bar{\Psi} M \Psi$ for a 4x4 matrix $M$.
-/
def spinorBilinear (Psi : DiracSpinor) (M : DiracMatrix) (Phi : DiracSpinor) : ℂ :=
  let barPsi := diracAdjoint Psi
  (barPsi 0 * (M 0 0 * Phi 0 + M 0 1 * Phi 1 + M 0 2 * Phi 2 + M 0 3 * Phi 3)) +
  (barPsi 1 * (M 1 0 * Phi 0 + M 1 1 * Phi 1 + M 1 2 * Phi 2 + M 1 3 * Phi 3)) +
  (barPsi 2 * (M 2 0 * Phi 0 + M 2 1 * Phi 1 + M 2 2 * Phi 2 + M 2 3 * Phi 3)) +
  (barPsi 3 * (M 3 0 * Phi 0 + M 3 1 * Phi 1 + M 3 2 * Phi 2 + M 3 3 * Phi 3))

/--
Coordinate expansion of the `gamma0` spinor bilinear.
-/
theorem gamma0_spinorBilinear_eq (Psi dPsi : DiracSpinor) :
    spinorBilinear Psi gamma0 dPsi = 
      (star Psi 0) * dPsi 0 + (star Psi 1) * dPsi 1 + 
      (star Psi 2) * dPsi 2 + (star Psi 3) * dPsi 3 := by
  simp [spinorBilinear, diracAdjoint, gamma0]
  try ring

/--
Coordinate expansion of the `gamma5 * gamma0` spinor bilinear.
-/
theorem gamma5_gamma0_spinorBilinear_eq (Psi : DiracSpinor) :
    spinorBilinear Psi (gamma5 * gamma0) Psi = 
      -(star Psi 0) * Psi 2 - (star Psi 1) * Psi 3 
      -(star Psi 2) * Psi 0 - (star Psi 3) * Psi 1 := by
  simp [spinorBilinear, diracAdjoint, gamma0, gamma1, gamma2, gamma3, gamma5, Matrix.mul_apply, Fin.sum_univ_succ, smul_apply, add_apply, sub_apply, one_apply]
  try ring

/--
Coordinate expansion of the `gamma5 * gamma1` spinor bilinear.
-/
theorem gamma5_gamma1_spinorBilinear_eq (Psi : DiracSpinor) :
    spinorBilinear Psi (gamma5 * gamma1) Psi = 
      -(star Psi 0) * Psi 1 - (star Psi 1) * Psi 0 
      -(star Psi 2) * Psi 3 - (star Psi 3) * Psi 2 := by
  simp [spinorBilinear, diracAdjoint, gamma0, gamma1, gamma2, gamma3, gamma5, Matrix.mul_apply, Fin.sum_univ_succ, smul_apply, add_apply, sub_apply, one_apply]
  try ring

end InfoGeometry.Canonical.EmergentSpinorElectromagnetism
