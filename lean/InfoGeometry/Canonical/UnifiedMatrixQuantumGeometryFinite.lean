import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite

Finite `2 × 2` Pauli-matrix owner for the matrix quantum-geometry notes.

This file deliberately proves only the algebraic matrix facts that close in the
Lean kernel.  It does not prove a continuum spacetime theory, diffeomorphism
invariance, Einstein equations from density matrices, an entanglement/holonomy
limit theorem, or a physical quantum-gravity model.

It also records a sign correction: the map
`i ↦ Complex.I • σ₁`, `j ↦ Complex.I • σ₂`, `k ↦ Complex.I • σ₃`
is not the standard quaternion multiplication table, because the first product
is `-Complex.I • σ₃`.  The corrected homomorphic finite basis used below is
`i ↦ Complex.I • σ₁`, `j ↦ Complex.I • σ₂`, `k ↦ -Complex.I • σ₃`.

#### BUCKET 1: CLOSED FINITE THEOREMS
Pauli square/product/trace identities, the quaternion sign obstruction and
corrected multiplication table, the Hermitian Pauli point determinant
`det(X)=1/2(t²-x²-y²-z²)`, the Minkowski determinant readback
`-2 det(X)=-t²+x²+y²+z²`, density-matrix determinant
`det(ρ)=1/4(1-|n|²)`, pure Bloch determinant zero from unit norm, and the
finite Bloch precession commutator formula.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`densityMatrix_det_zero_of_unit_bloch` depends on the explicit algebraic unit
Bloch premise `n1^2+n2^2+n3^2=1`.

#### BUCKET 3: OPEN CLOSURE DEBT
Hermitian positivity, rank classification, `CP^1 ≃ S^2` as a smooth
diffeomorphism, curved-spacetime connections, Einstein equations, area laws,
entanglement/connection correspondence, quantum evolution as spacetime
translation, and physical dynamics.
-/

namespace InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite

open Matrix
open Complex

noncomputable section

abbrev Mat2 : Type :=
  Matrix (Fin 2) (Fin 2) ℂ

@[simp] theorem complex_I_sq : (Complex.I : ℂ) ^ 2 = -1 := by
  rw [pow_two, Complex.I_mul_I]

/-- The `2 × 2` identity in the Pauli basis. -/
def σ0 : Mat2 :=
  1

/-- First Pauli matrix. -/
def σ1 : Mat2 :=
  !![(0 : ℂ), 1; 1, 0]

/-- Second Pauli matrix. -/
def σ2 : Mat2 :=
  !![(0 : ℂ), -Complex.I; Complex.I, 0]

/-- Third Pauli matrix. -/
def σ3 : Mat2 :=
  !![(1 : ℂ), 0; 0, -1]

/-- Pauli square identity for `σ1`. -/
theorem sigma1_sq : σ1 * σ1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli square identity for `σ2`. -/
theorem sigma2_sq : σ2 * σ2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Pauli square identity for `σ3`. -/
theorem sigma3_sq : σ3 * σ3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ3, Matrix.mul_apply, Fin.sum_univ_two]

/-- Product `σ1 σ2 = i σ3`. -/
theorem sigma1_mul_sigma2 : σ1 * σ2 = Complex.I • σ3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two]

/-- Product `σ2 σ3 = i σ1`. -/
theorem sigma2_mul_sigma3 : σ2 * σ3 = Complex.I • σ1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two]

/-- Product `σ3 σ1 = i σ2`. -/
theorem sigma3_mul_sigma1 : σ3 * σ1 = Complex.I • σ2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Pauli trace identity `Tr(σ1)=0`. -/
theorem trace_sigma1 : σ1.trace = 0 := by
  simp [Matrix.trace, σ1, Fin.sum_univ_two]

/-- Pauli trace identity `Tr(σ2)=0`. -/
theorem trace_sigma2 : trace σ2 = 0 := by
  simp [Matrix.trace, σ2, Fin.sum_univ_two]

/-- Pauli trace identity `Tr(σ3)=0`. -/
theorem trace_sigma3 : trace σ3 = 0 := by
  simp [Matrix.trace, σ3, Fin.sum_univ_two]

/-! ## Quaternion sign correction and corrected finite multiplication table -/

/-- The literal map `k ↦ iσ3` has the wrong `ij` sign. -/
theorem quaternion_literal_i_j_sign_obstruction :
    (Complex.I • σ1) * (Complex.I • σ2) = -(Complex.I • σ3) := by
  rw [smul_mul_smul, sigma1_mul_sigma2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ3, Complex.I_mul_I]

/-- Corrected quaternion `i` basis matrix. -/
def qI : Mat2 :=
  Complex.I • σ1

/-- Corrected quaternion `j` basis matrix. -/
def qJ : Mat2 :=
  Complex.I • σ2

/-- Corrected quaternion `k` basis matrix. -/
def qK : Mat2 :=
  -Complex.I • σ3

theorem qI_sq : qI * qI = -1 := by
  unfold qI
  rw [smul_mul_smul, sigma1_sq, Complex.I_mul_I]
  simp

theorem qJ_sq : qJ * qJ = -1 := by
  unfold qJ
  rw [smul_mul_smul, sigma2_sq, Complex.I_mul_I]
  simp

theorem qK_sq : qK * qK = -1 := by
  unfold qK
  rw [smul_mul_smul, sigma3_sq]
  simp [Complex.I_mul_I]

theorem qI_mul_qJ : qI * qJ = qK := by
  unfold qI qJ qK
  rw [smul_mul_smul, sigma1_mul_sigma2, Complex.I_mul_I]
  simp

theorem qJ_mul_qK : qJ * qK = qI := by
  unfold qI qJ qK
  rw [smul_mul_smul, sigma2_mul_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, Complex.I_mul_I]

theorem qK_mul_qI : qK * qI = qJ := by
  unfold qI qJ qK
  rw [smul_mul_smul, sigma3_mul_sigma1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ2, Complex.I_mul_I]

/-! ## Hermitian Pauli point and Minkowski determinant readout -/

/-- Pauli spacetime matrix without the irrational normalization. -/
def pauliPointRaw (t x y z : ℂ) : Mat2 :=
  !![t + z, x - Complex.I * y; x + Complex.I * y, t - z]

/-- Normalized Pauli spacetime matrix `1/sqrt(2)` at the determinant level. -/
def pauliPointDet (t x y z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (pauliPointRaw t x y z).det

/-- Determinant of the raw Hermitian Pauli point. -/
theorem pauliPointRaw_det (t x y z : ℂ) :
    (pauliPointRaw t x y z).det = t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [pauliPointRaw, Matrix.det_fin_two]
  ring_nf
  rw [complex_I_sq]
  ring_nf

/-- Determinant of the normalized Pauli point. -/
theorem pauliPointDet_eq (t x y z : ℂ) :
    pauliPointDet t x y z = (1 / 2 : ℂ) * (t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) := by
  rw [pauliPointDet, pauliPointRaw_det]

/-- The Pauli determinant recovers the `(-,+,+,+)` Minkowski quadratic form. -/
theorem minkowski_readout_eq_neg_two_det (t x y z : ℂ) :
    -2 * pauliPointDet t x y z = -t ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 := by
  rw [pauliPointDet_eq]
  ring

/-! ## Density matrix determinant and pure-state finite shadow -/

/-- Qubit density-matrix algebraic readout from a Bloch vector. -/
def densityMatrix (n1 n2 n3 : ℂ) : Mat2 :=
  !![(1 + n3) / 2, (n1 - Complex.I * n2) / 2;
     (n1 + Complex.I * n2) / 2, (1 - n3) / 2]

/-- Determinant of the Bloch density matrix. -/
theorem densityMatrix_det (n1 n2 n3 : ℂ) :
    (densityMatrix n1 n2 n3).det =
      (1 / 4 : ℂ) * (1 - (n1 ^ 2 + n2 ^ 2 + n3 ^ 2)) := by
  simp [densityMatrix, Matrix.det_fin_two]
  ring_nf
  rw [complex_I_sq]
  ring_nf

/-- Unit Bloch norm implies the algebraic pure-state determinant obstruction vanishes. -/
theorem densityMatrix_det_zero_of_unit_bloch (n1 n2 n3 : ℂ)
    (hunit : n1 ^ 2 + n2 ^ 2 + n3 ^ 2 = 1) :
    (densityMatrix n1 n2 n3).det = 0 := by
  rw [densityMatrix_det, hunit]
  ring

/-! ## Finite Bloch precession commutator -/

/-- Pauli Hamiltonian `H = 1/2 ω·σ`. -/
def pauliHamiltonian (ω1 ω2 ω3 : ℂ) : Mat2 :=
  !![ω3 / 2, (ω1 - Complex.I * ω2) / 2;
     (ω1 + Complex.I * ω2) / 2, -ω3 / 2]

/-- Von-Neumann right-hand side `-i[H,ρ]`. -/
def vonNeumannRHS (ω1 ω2 ω3 n1 n2 n3 : ℂ) : Mat2 :=
  -Complex.I •
    (pauliHamiltonian ω1 ω2 ω3 * densityMatrix n1 n2 n3 -
      densityMatrix n1 n2 n3 * pauliHamiltonian ω1 ω2 ω3)

/-- Bloch-vector cross-product readout `ω × n`. -/
def blochCross1 (_ω1 ω2 ω3 _n1 n2 n3 : ℂ) : ℂ :=
  ω2 * n3 - ω3 * n2

def blochCross2 (ω1 _ω2 ω3 n1 _n2 n3 : ℂ) : ℂ :=
  ω3 * n1 - ω1 * n3

def blochCross3 (ω1 ω2 _ω3 n1 n2 _n3 : ℂ) : ℂ :=
  ω1 * n2 - ω2 * n1

/-- The finite von-Neumann commutator gives Bloch precession. -/
theorem vonNeumannRHS_eq_bloch_precession (ω1 ω2 ω3 n1 n2 n3 : ℂ) :
    vonNeumannRHS ω1 ω2 ω3 n1 n2 n3 =
      (1 / 2 : ℂ) •
        (blochCross1 ω1 ω2 ω3 n1 n2 n3 • σ1 +
          blochCross2 ω1 ω2 ω3 n1 n2 n3 • σ2 +
          blochCross3 ω1 ω2 ω3 n1 n2 n3 • σ3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vonNeumannRHS, pauliHamiltonian, densityMatrix,
      blochCross1, blochCross2, blochCross3,
      σ1, σ2, σ3]
    <;> ring_nf
    <;> rw [complex_I_sq]
    <;> ring_nf

end

end InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
