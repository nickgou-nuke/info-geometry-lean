import Mathlib.Data.Complex.Basic
import InfoGeometry.Clifford.DiracPauliGamma
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.SpinorGradeParityEscape

This module records a finite owner-level escape from the bare Clifford-trace
grade-parity obstruction. The obstruction itself says that odd-graded bare
traces vanish on an even-graded quaternionic condensate lane. The honest finite
repair is not to fake a nonzero bare trace, but to pass to Dirac spinor
bilinears `Ψ̄ M Φ`, where the spinor degrees of freedom can produce nonzero
axial readouts.

#### BUCKET 1: CLOSED FINITE THEOREMS

* exact closed forms for `Ψ̄ γ0 dΨ`, `Ψ̄ (γ5 γ0) Ψ`, and `Ψ̄ (γ5 γ1) Ψ`;
* explicit nonzero witnesses for the temporal vielbein and two axial channels;
* scalar linearity of the axial temporal insertion.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not construct a continuum `U(1)` bundle, Maxwell dynamics,
Einstein-Cartan equations, or a non-Abelian gauge theory. It only proves the
finite spinor-bilinear escape route.
-/

namespace InfoGeometry.Canonical.SpinorGradeParityEscape

open Complex
open InfoGeometry.Clifford.DiracPauliGamma

/-- Dirac adjoint row `Ψ̄ = Ψ† γ0`. -/
def diracAdjoint (Psi : DiracSpinor) : Fin 4 → ℂ :=
  fun j =>
    (star Psi 0) * gamma0 0 j +
      (star Psi 1) * gamma0 1 j +
        (star Psi 2) * gamma0 2 j + (star Psi 3) * gamma0 3 j

/-- Finite Dirac bilinear `Ψ̄ M Φ`. -/
def spinorBilinear (Psi : DiracSpinor) (M : DiracMatrix) (Phi : DiracSpinor) : ℂ :=
  let barPsi := diracAdjoint Psi
  (barPsi 0 * (M 0 0 * Phi 0 + M 0 1 * Phi 1 + M 0 2 * Phi 2 + M 0 3 * Phi 3)) +
    (barPsi 1 * (M 1 0 * Phi 0 + M 1 1 * Phi 1 + M 1 2 * Phi 2 + M 1 3 * Phi 3)) +
      (barPsi 2 * (M 2 0 * Phi 0 + M 2 1 * Phi 1 + M 2 2 * Phi 2 + M 2 3 * Phi 3)) +
        (barPsi 3 *
          (M 3 0 * Phi 0 + M 3 1 * Phi 1 + M 3 2 * Phi 2 + M 3 3 * Phi 3))

/-- Closed form for the temporal vielbein readout `Ψ̄ γ0 dΨ`. -/
theorem temporalVielbein_closed_form (Psi dPsi : DiracSpinor) :
    spinorBilinear Psi gamma0 dPsi =
      (star Psi 0) * dPsi 0 +
        (star Psi 1) * dPsi 1 + (star Psi 2) * dPsi 2 + (star Psi 3) * dPsi 3 := by
  simp [spinorBilinear, diracAdjoint, gamma0]

/-- Closed form for the temporal axial readout `Ψ̄ (γ5 γ0) Ψ`. -/
theorem temporalAxial_closed_form (Psi : DiracSpinor) :
    spinorBilinear Psi (gamma5 * gamma0) Psi =
      -(star Psi 0) * Psi 2 -
        (star Psi 1) * Psi 3 - (star Psi 2) * Psi 0 - (star Psi 3) * Psi 1 := by
  simp [spinorBilinear, diracAdjoint, gamma0, gamma5, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Closed form for the spatial axial readout `Ψ̄ (γ5 γ1) Ψ`. -/
theorem spatialAxial_closed_form (Psi : DiracSpinor) :
    spinorBilinear Psi (gamma5 * gamma1) Psi =
      -(star Psi 0) * Psi 1 -
        (star Psi 1) * Psi 0 - (star Psi 2) * Psi 3 - (star Psi 3) * Psi 2 := by
  simp [spinorBilinear, diracAdjoint, gamma0, gamma1, gamma5, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- The temporal vielbein witness evaluates exactly to `1`. -/
theorem temporalVielbein_gravityWitness_eval :
    spinorBilinear (![1, 0, 0, 0] : DiracSpinor) gamma0
        (![1, 0, 0, 0] : DiracSpinor) = 1 := by
  rw [temporalVielbein_closed_form]
  simp

/-- The temporal axial witness evaluates exactly to `-2`. -/
theorem temporalAxial_temporalWitness_eval :
    spinorBilinear (![1, 0, 1, 0] : DiracSpinor) (gamma5 * gamma0)
        (![1, 0, 1, 0] : DiracSpinor) = -2 := by
  rw [temporalAxial_closed_form]
  simp
  ring_nf

/-- The spatial axial witness evaluates exactly to `-2`. -/
theorem spatialAxial_spatialWitness_eval :
    spinorBilinear (![1, 1, 0, 0] : DiracSpinor) (gamma5 * gamma1)
        (![1, 1, 0, 0] : DiracSpinor) = -2 := by
  rw [spatialAxial_closed_form]
  simp
  ring_nf

/-- The temporal vielbein witness is genuinely nonzero. -/
theorem temporalVielbein_gravityWitness_ne_zero :
    spinorBilinear (![1, 0, 0, 0] : DiracSpinor) gamma0
        (![1, 0, 0, 0] : DiracSpinor) ≠ 0 := by
  rw [temporalVielbein_gravityWitness_eval]
  norm_num

/-- The temporal axial witness is genuinely nonzero. -/
theorem temporalAxial_temporalWitness_ne_zero :
    spinorBilinear (![1, 0, 1, 0] : DiracSpinor) (gamma5 * gamma0)
        (![1, 0, 1, 0] : DiracSpinor) ≠ 0 := by
  rw [temporalAxial_temporalWitness_eval]
  norm_num

/-- The spatial axial witness is genuinely nonzero. -/
theorem spatialAxial_spatialWitness_ne_zero :
    spinorBilinear (![1, 1, 0, 0] : DiracSpinor) (gamma5 * gamma1)
        (![1, 1, 0, 0] : DiracSpinor) ≠ 0 := by
  rw [spatialAxial_spatialWitness_eval]
  norm_num

/-- Scalar linearity for the temporal axial insertion in the second slot. -/
theorem temporalAxial_smul_right (a : ℂ) (Psi : DiracSpinor) :
    spinorBilinear Psi (gamma5 * gamma0) (fun i => a * Psi i) =
      a * spinorBilinear Psi (gamma5 * gamma0) Psi := by
  simp [spinorBilinear, diracAdjoint, gamma0, gamma5, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

end InfoGeometry.Canonical.SpinorGradeParityEscape
