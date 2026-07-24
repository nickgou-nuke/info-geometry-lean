import Mathlib.Data.Complex.Basic
import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Canonical.EmergentSpinorElectromagnetism

/-!
# InfoGeometry.Canonical.EmergentNonAbelianGauge

This module proves a scalar-factorization identity for a coordinate spinor
bilinear with a supplied scalar insertion.  It does not construct non-Abelian
gauge fields, SU(2)/SU(3) dynamics, or Standard Model interactions.
-/

namespace InfoGeometry.Canonical.EmergentNonAbelianGauge

open Matrix
open Complex
open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Canonical.EmergentSpinorElectromagnetism

/--
A scalar insertion in the spinor bilinear coordinates.
-/
def gaugeInsertionBilinear (Psi : DiracSpinor) (M : DiracMatrix) (Ta : ℂ) : ℂ :=
  let barPsi := diracAdjoint Psi
  (barPsi 0 * (M 0 0 * (Ta * Psi 0) + M 0 1 * (Ta * Psi 1) + M 0 2 * (Ta * Psi 2) + M 0 3 * (Ta * Psi 3))) +
  (barPsi 1 * (M 1 0 * (Ta * Psi 0) + M 1 1 * (Ta * Psi 1) + M 1 2 * (Ta * Psi 2) + M 1 3 * (Ta * Psi 3))) +
  (barPsi 2 * (M 2 0 * (Ta * Psi 0) + M 2 1 * (Ta * Psi 1) + M 2 2 * (Ta * Psi 2) + M 2 3 * (Ta * Psi 3))) +
  (barPsi 3 * (M 3 0 * (Ta * Psi 0) + M 3 1 * (Ta * Psi 1) + M 3 2 * (Ta * Psi 2) + M 3 3 * (Ta * Psi 3)))

/--
A scalar insertion factors out of this bilinear expression.
-/
theorem gaugeInsertionBilinear_scalar_factor (Psi : DiracSpinor) (Ta : ℂ) :
    gaugeInsertionBilinear Psi (gamma5 * gamma0) Ta = 
      Ta * spinorBilinear Psi (gamma5 * gamma0) Psi := by
  dsimp [gaugeInsertionBilinear, spinorBilinear]
  ring

end InfoGeometry.Canonical.EmergentNonAbelianGauge
