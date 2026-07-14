import InfoGeometry.UnifiedMatrixBasis
import InfoGeometry.Physics.MD20250430071017MatrixStatistics

/-!
# Repaired MD 001: matrix quantum geometry introduction

Source: `github-nick:nickgou-nuke/MD`, file `001.md`.

The source is Chapter 1 of a handbook and is mostly a roadmap.  Its rigorous
finite core is already present in the repository: Pauli matrices, their basic
algebra, the determinant/Minkowski quadratic readout, the Hilbert--Schmidt
Pauli-basis trace readout, finite Bloch density algebra, and the later local
matrix-statistics bridge.

This file packages exactly that theorem-safe core.  It does not assert the
roadmap's exploratory claims about quantum gravity, hyperkähler/Kähler-Einstein
geometry, path integrals, emergent Einstein equations, TriSpin, measurement, or
black-hole information.  The null/pure-state statement is formalized only as
an algebraic Bloch-radius idempotence/determinant-zero identity, not as a
Born-rule or physical-state theorem.
-/

noncomputable section

namespace InfoGeometry.Physics.MD001MatrixQuantumGeometry

open Matrix
open InfoGeometry.Physics.MD20250430071017MatrixStatistics

set_option linter.unnecessarySeqFocus false

/-- The concrete `2 × 2` complex matrix carrier emphasized in `001.md`. -/
abbrev MatrixQuantumCarrier := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli-basis representative of a four-coordinate vector. -/
def pauliSpacetimeMatrix (dt dx dy dz : ℂ) : MatrixQuantumCarrier :=
  dt • UnifiedMatrixBasis.I₂ + dx • UnifiedMatrixBasis.σ₁ +
    dy • UnifiedMatrixBasis.σ₂ + dz • UnifiedMatrixBasis.σ₃

/-- The Pauli/Hermitian determinant readout is the finite Minkowski quadratic form. -/
theorem pauliSpacetimeMatrix_det (dt dx dy dz : ℂ) :
    Matrix.det (pauliSpacetimeMatrix dt dx dy dz) =
      dt * dt - (dx * dx + dy * dy + dz * dz) := by
  simpa [pauliSpacetimeMatrix] using
    UnifiedMatrixBasis.metric_equivalence dt dx dy dz

/-- The Pauli spatial generators square to the identity. -/
theorem md001_pauli_square_sigma1 :
    UnifiedMatrixBasis.σ₁ * UnifiedMatrixBasis.σ₁ = UnifiedMatrixBasis.I₂ :=
  UnifiedMatrixBasis.pauli_square.1

theorem md001_pauli_square_sigma2 :
    UnifiedMatrixBasis.σ₂ * UnifiedMatrixBasis.σ₂ = UnifiedMatrixBasis.I₂ :=
  UnifiedMatrixBasis.pauli_square.2.1

theorem md001_pauli_square_sigma3 :
    UnifiedMatrixBasis.σ₃ * UnifiedMatrixBasis.σ₃ = UnifiedMatrixBasis.I₂ :=
  UnifiedMatrixBasis.pauli_square.2.2

/-- Distinct Pauli spatial generators anticommute in the three cyclic pairs. -/
theorem md001_pauli_anticomm_12 :
    UnifiedMatrixBasis.σ₁ * UnifiedMatrixBasis.σ₂ +
        UnifiedMatrixBasis.σ₂ * UnifiedMatrixBasis.σ₁ = 0 :=
  UnifiedMatrixBasis.pauli_anticomm.1

theorem md001_pauli_anticomm_23 :
    UnifiedMatrixBasis.σ₂ * UnifiedMatrixBasis.σ₃ +
        UnifiedMatrixBasis.σ₃ * UnifiedMatrixBasis.σ₂ = 0 :=
  UnifiedMatrixBasis.pauli_anticomm.2.1

theorem md001_pauli_anticomm_31 :
    UnifiedMatrixBasis.σ₃ * UnifiedMatrixBasis.σ₁ +
        UnifiedMatrixBasis.σ₁ * UnifiedMatrixBasis.σ₃ = 0 :=
  UnifiedMatrixBasis.pauli_anticomm.2.2

/-- The normalized trace/Hilbert--Schmidt readout normalizes the identity and Pauli axes. -/
theorem md001_hilbertSchmidt_I2_I2 :
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.I₂ UnifiedMatrixBasis.I₂ = (1 : ℂ) :=
  UnifiedMatrixBasis.hilbertSchmidt_orthonormal.1

theorem md001_hilbertSchmidt_sigma1_sigma1 :
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.σ₁ UnifiedMatrixBasis.σ₁ = (1 : ℂ) :=
  UnifiedMatrixBasis.hilbertSchmidt_orthonormal.2.1

theorem md001_hilbertSchmidt_sigma2_sigma2 :
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.σ₂ UnifiedMatrixBasis.σ₂ = (1 : ℂ) :=
  UnifiedMatrixBasis.hilbertSchmidt_orthonormal.2.2.1

theorem md001_hilbertSchmidt_sigma3_sigma3 :
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.σ₃ UnifiedMatrixBasis.σ₃ = (1 : ℂ) :=
  UnifiedMatrixBasis.hilbertSchmidt_orthonormal.2.2.2.1

theorem md001_hilbertSchmidt_I2_sigma1 :
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.I₂ UnifiedMatrixBasis.σ₁ = 0 :=
  UnifiedMatrixBasis.hilbertSchmidt_orthonormal.2.2.2.2

/-- Finite Bloch-form density matrix `ρ = 1/2(I + xσ₁ + yσ₂ + zσ₃)`. -/
def blochDensity (x y z : ℂ) : MatrixQuantumCarrier :=
  (1 / 2 : ℂ) •
    (UnifiedMatrixBasis.I₂ + x • UnifiedMatrixBasis.σ₁ +
      y • UnifiedMatrixBasis.σ₂ + z • UnifiedMatrixBasis.σ₃)

/-- Bloch-form density has trace one as a finite algebraic identity. -/
theorem blochDensity_trace_one (x y z : ℂ) :
    Matrix.trace (blochDensity x y z) = 1 := by
  simp [blochDensity, UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁,
    UnifiedMatrixBasis.σ₂, UnifiedMatrixBasis.σ₃, Matrix.trace, Fin.sum_univ_two]
  ring

/-- Bloch-form determinant is `1/4 * (1 - radius²)`. -/
theorem blochDensity_det (x y z : ℂ) :
    Matrix.det (blochDensity x y z) = (1 / 4 : ℂ) * (1 - (x * x + y * y + z * z)) := by
  rw [Matrix.det_fin_two]
  simp [blochDensity, UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁,
    UnifiedMatrixBasis.σ₂, UnifiedMatrixBasis.σ₃]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Algebraic unit Bloch radius gives an idempotent matrix. -/
theorem blochDensity_idempotent_of_unit (x y z : ℂ)
    (hunit : x * x + y * y + z * z = 1) :
    blochDensity x y z * blochDensity x y z = blochDensity x y z := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [blochDensity, UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁,
      UnifiedMatrixBasis.σ₂, UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  · ring_nf at hunit ⊢
    rw [Complex.I_sq]
    ring_nf
    linear_combination hunit / 4
  · ring
  · ring
  · ring_nf at hunit ⊢
    rw [Complex.I_sq]
    ring_nf
    linear_combination hunit / 4

/-- Algebraic unit Bloch radius also gives determinant zero. -/
theorem blochDensity_det_zero_of_unit (x y z : ℂ)
    (hunit : x * x + y * y + z * z = 1) :
    Matrix.det (blochDensity x y z) = 0 := by
  rw [blochDensity_det, hunit]
  ring

/-- Any concrete local matrix configuration is recovered from its Pauli coefficients. -/
theorem md001_local_matrix_recompose (A : LocalMatrixConfig) :
    InfoGeometry.Physics.Section33PauliBiquaternionCompletion.pauliRecompose A = A :=
  localMatrix_recompose A

end InfoGeometry.Physics.MD001MatrixQuantumGeometry

end noncomputable section
