import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Canonical.EmergentSpinorElectromagnetism

/-!
# InfoGeometry.Canonical.EmergentNonAbelianGauge

This module records the finite scalar-insertion bridge for spinor bilinears and
the first concrete non-Abelian generator checks. It does not construct gauge
bundles, Yang-Mills curvature, or physical weak/strong fields. The closed
theorems are finite matrix identities and explicit nonzero witnesses on the
spinor-bilinear surface.

#### BUCKET 1: CLOSED FINITE THEOREMS
Scalar insertion into the right spinor argument factors out of the Dirac
bilinear for any concrete matrix on the doubled carrier. The Pauli matrices
satisfy the full finite commutator cycle `[τ₁, τ₂] = 2i τ₃`,
`[τ₂, τ₃] = 2i τ₁`, and `[τ₃, τ₁] = 2i τ₂`; the first Gell-Mann cycle checks
`[λ₁, λ₂] = 2i λ₃`, `[λ₂, λ₃] = 2i λ₁`, and `[λ₃, λ₁] = 2i λ₂`. The first
generators are nonzero. Concrete spinor witnesses give nonzero axial bilinears
after scalar insertion.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Full bases, all structure constants, representations on internal spinor/color
bundles, curvature, Yang-Mills equations, and physical SU(2)/SU(3) gauge
dynamics are not proved here.
-/

namespace InfoGeometry.Canonical.EmergentNonAbelianGauge

open Matrix
open Complex
open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Canonical.EmergentSpinorElectromagnetism

/-- Concrete `2 × 2` complex matrix carrier for the first weak-isospin checks. -/
abbrev IsoMatrix : Type :=
  Matrix (Fin 2) (Fin 2) ℂ

/-- Concrete `3 × 3` complex matrix carrier for the first color checks. -/
abbrev ColorMatrix : Type :=
  Matrix (Fin 3) (Fin 3) ℂ

/-- The first Pauli matrix. -/
def tau1 : IsoMatrix :=
  !![(0 : ℂ), 1; 1, 0]

/-- The second Pauli matrix. -/
def tau2 : IsoMatrix :=
  !![(0 : ℂ), -Complex.I; Complex.I, 0]

/-- The third Pauli matrix. -/
def tau3 : IsoMatrix :=
  !![(1 : ℂ), 0; 0, -1]

/-- The first Gell-Mann matrix. -/
def lambda1 : ColorMatrix :=
  !![(0 : ℂ), 1, 0; 1, 0, 0; 0, 0, 0]

/-- The second Gell-Mann matrix. -/
def lambda2 : ColorMatrix :=
  !![(0 : ℂ), -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]

/-- The third Gell-Mann matrix. -/
def lambda3 : ColorMatrix :=
  !![(1 : ℂ), 0, 0; 0, -1, 0; 0, 0, 0]

/-- Matrix commutator. -/
def matrixBracket {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  A * B - B * A

/-- The first Pauli commutator closes on the third Pauli generator. -/
theorem tau12_bracket :
    matrixBracket tau1 tau2 = (2 * Complex.I : ℂ) • tau3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBracket, tau1, tau2, tau3]
  all_goals ring_nf

/-- The second Pauli commutator closes on the first Pauli generator. -/
theorem tau23_bracket :
    matrixBracket tau2 tau3 = (2 * Complex.I : ℂ) • tau1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBracket, tau1, tau2, tau3] <;>
    ring_nf <;>
    norm_num [Complex.I_mul_I]

/-- The third Pauli commutator closes on the second Pauli generator. -/
theorem tau31_bracket :
    matrixBracket tau3 tau1 = (2 * Complex.I : ℂ) • tau2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBracket, tau1, tau2, tau3] <;>
    ring_nf <;>
    norm_num [Complex.I_mul_I]

/-- The first Gell-Mann commutator closes on the third Gell-Mann generator. -/
theorem lambda12_bracket :
    matrixBracket lambda1 lambda2 = (2 * Complex.I : ℂ) • lambda3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBracket, lambda1, lambda2, lambda3]
  all_goals ring_nf

/-- The second Gell-Mann commutator closes on the first Gell-Mann generator. -/
theorem lambda23_bracket :
    matrixBracket lambda2 lambda3 = (2 * Complex.I : ℂ) • lambda1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBracket, lambda1, lambda2, lambda3] <;>
    ring_nf <;>
    norm_num [Complex.I_mul_I]

/-- The third Gell-Mann commutator closes on the second Gell-Mann generator. -/
theorem lambda31_bracket :
    matrixBracket lambda3 lambda1 = (2 * Complex.I : ℂ) • lambda2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBracket, lambda1, lambda2, lambda3] <;>
    ring_nf <;>
    norm_num [Complex.I_mul_I]

/-- The first Pauli generator is not the zero matrix. -/
theorem tau1_ne_zero : tau1 ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [tau1] at h01

/-- The first Gell-Mann generator is not the zero matrix. -/
theorem lambda1_ne_zero : lambda1 ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [lambda1] at h01

/--
Scalar insertion into the right spinor argument of the bilinear.
-/
def gaugeInsertionBilinear (Psi : DiracSpinor) (M : DiracMatrix) (Ta : ℂ) : ℂ :=
  let barPsi := diracAdjoint Psi
  (barPsi 0 * (M 0 0 * (Ta * Psi 0) + M 0 1 * (Ta * Psi 1) + M 0 2 * (Ta * Psi 2) + M 0 3 * (Ta * Psi 3))) +
  (barPsi 1 * (M 1 0 * (Ta * Psi 0) + M 1 1 * (Ta * Psi 1) + M 1 2 * (Ta * Psi 2) + M 1 3 * (Ta * Psi 3))) +
  (barPsi 2 * (M 2 0 * (Ta * Psi 0) + M 2 1 * (Ta * Psi 1) + M 2 2 * (Ta * Psi 2) + M 2 3 * (Ta * Psi 3))) +
  (barPsi 3 * (M 3 0 * (Ta * Psi 0) + M 3 1 * (Ta * Psi 1) + M 3 2 * (Ta * Psi 2) + M 3 3 * (Ta * Psi 3)))

/--
Scalar insertion factors out of the right spinor argument for any concrete
matrix insertion.
-/
theorem scalar_insertion_factors (Psi : DiracSpinor) (M : DiracMatrix) (Ta : ℂ) :
    gaugeInsertionBilinear Psi M Ta = Ta * spinorBilinear Psi M Psi := by
  dsimp [gaugeInsertionBilinear, spinorBilinear]
  ring

/--
The scalar insertion factors out of the temporal axial spinor bilinear.
-/
theorem scalar_insertion_factors_temporal_axial (Psi : DiracSpinor) (Ta : ℂ) :
    gaugeInsertionBilinear Psi (gamma5 * gamma0) Ta =
      Ta * spinorBilinear Psi (gamma5 * gamma0) Psi := by
  simpa using scalar_insertion_factors Psi (gamma5 * gamma0) Ta

/-- A concrete temporal axial witness remains nonzero after scalar insertion. -/
theorem scalar_insertion_temporal_witness_nonzero :
    gaugeInsertionBilinear
        spinorWitnessTemporal (gamma5 * gamma0) (1 : ℂ) = -2 := by
  rw [scalar_insertion_factors_temporal_axial]
  simpa using a_mu_temporal_witness_nonzero

/-- A concrete spatial axial witness remains nonzero after scalar insertion. -/
theorem scalar_insertion_spatial_witness_nonzero :
    gaugeInsertionBilinear
        spinorWitnessSpatial (gamma5 * gamma1) (1 : ℂ) = -2 := by
  rw [scalar_insertion_factors]
  simpa using a_mu_spatial_witness_nonzero

end InfoGeometry.Canonical.EmergentNonAbelianGauge
