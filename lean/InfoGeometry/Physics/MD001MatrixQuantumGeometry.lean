import InfoGeometry.UnifiedMatrixBasis
import InfoGeometry.Physics.MD20250430071017MatrixStatistics

/-!
# Repaired MD 001: matrix quantum geometry introduction

Source: `github-nick:nickgou-nuke/MD`, file `001.md`.

The source is Chapter 1 of a handbook and is mostly a roadmap.  Its rigorous
finite core is already present in the repository: Pauli matrices, their basic
algebra, the determinant/Minkowski quadratic readout, the Hilbert--Schmidt
Pauli-basis trace readout, and the later local matrix-statistics bridge.

This file packages exactly that theorem-safe core.  It does not assert the
roadmap's exploratory claims about quantum gravity, hyperkähler/Kähler-Einstein
geometry, path integrals, emergent Einstein equations, TriSpin, measurement, or
black-hole information.
-/

noncomputable section

namespace InfoGeometry.Physics.MD001MatrixQuantumGeometry

open Matrix
open InfoGeometry.Physics.MD20250430071017MatrixStatistics

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
theorem md001_pauli_square_packet :
    UnifiedMatrixBasis.σ₁ * UnifiedMatrixBasis.σ₁ = UnifiedMatrixBasis.I₂ ∧
    UnifiedMatrixBasis.σ₂ * UnifiedMatrixBasis.σ₂ = UnifiedMatrixBasis.I₂ ∧
    UnifiedMatrixBasis.σ₃ * UnifiedMatrixBasis.σ₃ = UnifiedMatrixBasis.I₂ :=
  UnifiedMatrixBasis.pauli_square

/-- Distinct Pauli spatial generators anticommute in the three cyclic pairs. -/
theorem md001_pauli_anticomm_packet :
    UnifiedMatrixBasis.σ₁ * UnifiedMatrixBasis.σ₂ +
        UnifiedMatrixBasis.σ₂ * UnifiedMatrixBasis.σ₁ = 0 ∧
    UnifiedMatrixBasis.σ₂ * UnifiedMatrixBasis.σ₃ +
        UnifiedMatrixBasis.σ₃ * UnifiedMatrixBasis.σ₂ = 0 ∧
    UnifiedMatrixBasis.σ₃ * UnifiedMatrixBasis.σ₁ +
        UnifiedMatrixBasis.σ₁ * UnifiedMatrixBasis.σ₃ = 0 :=
  UnifiedMatrixBasis.pauli_anticomm

/-- The normalized trace/Hilbert--Schmidt readout normalizes the identity and Pauli axes. -/
theorem md001_hilbertSchmidt_packet :
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.I₂ UnifiedMatrixBasis.I₂ = (1 : ℂ) ∧
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.σ₁ UnifiedMatrixBasis.σ₁ = (1 : ℂ) ∧
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.σ₂ UnifiedMatrixBasis.σ₂ = (1 : ℂ) ∧
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.σ₃ UnifiedMatrixBasis.σ₃ = (1 : ℂ) ∧
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.I₂ UnifiedMatrixBasis.σ₁ = 0 :=
  UnifiedMatrixBasis.hilbertSchmidt_orthonormal

/-- Any concrete local matrix configuration is recovered from its Pauli coefficients. -/
theorem md001_local_matrix_recompose (A : LocalMatrixConfig) :
    InfoGeometry.Physics.Section33PauliBiquaternionCompletion.pauliRecompose A = A :=
  localMatrix_recompose A

/-- Repaired theorem-safe Chapter 1 packet. -/
theorem repaired_MD001_matrix_quantum_geometry_packet (dt dx dy dz : ℂ)
    (A : LocalMatrixConfig) :
    Matrix.det (pauliSpacetimeMatrix dt dx dy dz) =
        dt * dt - (dx * dx + dy * dy + dz * dz) ∧
    UnifiedMatrixBasis.σ₁ * UnifiedMatrixBasis.σ₁ = UnifiedMatrixBasis.I₂ ∧
    UnifiedMatrixBasis.σ₁ * UnifiedMatrixBasis.σ₂ +
        UnifiedMatrixBasis.σ₂ * UnifiedMatrixBasis.σ₁ = 0 ∧
    UnifiedMatrixBasis.hilbertSchmidt UnifiedMatrixBasis.I₂ UnifiedMatrixBasis.I₂ = (1 : ℂ) ∧
    InfoGeometry.Physics.Section33PauliBiquaternionCompletion.pauliRecompose A = A := by
  exact ⟨pauliSpacetimeMatrix_det dt dx dy dz,
    md001_pauli_square_packet.1,
    md001_pauli_anticomm_packet.1,
    md001_hilbertSchmidt_packet.1,
    md001_local_matrix_recompose A⟩

end InfoGeometry.Physics.MD001MatrixQuantumGeometry

end noncomputable section
