import InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite

/-!
# Finite Q₈ Pauli representation

This module exposes the corrected quaternion-group multiplication surface from
the canonical finite Pauli owner.  The faithful signs are
`qI = iσ₁`, `qJ = iσ₂`, and `qK = -iσ₃`.
-/

noncomputable section

namespace Q8NuclearChirality

open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite

abbrev M2C := Mat2
abbrev sigma1 : M2C := σ1
abbrev sigma2 : M2C := σ2
abbrev sigma3 : M2C := σ3

/-- The Pauli generators square to the identity and obey the oriented triple
product. -/
theorem pauli_relations :
    sigma1 * sigma1 = (1 : M2C) ∧
    sigma2 * sigma2 = (1 : M2C) ∧
    sigma3 * sigma3 = (1 : M2C) ∧
    sigma1 * sigma2 * sigma3 = Complex.I • (1 : M2C) := by
  refine ⟨sigma1_sq, sigma2_sq, sigma3_sq, ?_⟩
  rw [sigma1_mul_sigma2]
  simpa [Algebra.smul_mul_assoc, sigma3_sq]

/-- Corrected Q₈ basis relations, including the sign of `qK`. -/
theorem q8_quaternion_relations :
    qI * qI = -(1 : M2C) ∧
    qJ * qJ = -(1 : M2C) ∧
    qK * qK = -(1 : M2C) ∧
    qI * qJ = qK ∧
    qJ * qK = qI ∧
    qK * qI = qJ :=
  ⟨qI_sq, qJ_sq, qK_sq, qI_mul_qJ, qJ_mul_qK, qK_mul_qI⟩

/-- The two first quaternion generators exhibit the fermionic double-cover
square relation. -/
theorem fermionic_double_cover :
    qI * qI = -(1 : M2C) ∧ qJ * qJ = -(1 : M2C) :=
  ⟨qI_sq, qJ_sq⟩

/-- The corrected third quaternion generator also squares to `-1`. -/
theorem chiral_square_fermionic : qK * qK = -(1 : M2C) :=
  qK_sq

end Q8NuclearChirality

end noncomputable section
