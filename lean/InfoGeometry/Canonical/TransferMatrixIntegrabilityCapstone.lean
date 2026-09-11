import InfoGeometry.Quantum.TransferMatrixIntegrability
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.TransferMatrixIntegrabilityCapstone

open InfoGeometry.Quantum.TransferMatrixIntegrability

theorem capstone_transfer_matrix_integrability_synthesis
    (Γ Γ₁ Γ₂ u v : ℝ) :
    (quantumTransferMatrix Γ u = ((quantumTransferMatrixReal Γ u : ℝ) : ℂ)) ∧
    (quantumTransferMatrixReal Γ 0 = 2) ∧
    (quantumTransferMatrixReal Γ (-u) = quantumTransferMatrixReal Γ u) ∧
    (laxPhaseFactor (Γ₁ + Γ₂) u = laxPhaseFactor Γ₁ u * laxPhaseFactor Γ₂ u) ∧
    (quantumTransferMatrix Γ u * quantumTransferMatrix Γ v -
     quantumTransferMatrix Γ v * quantumTransferMatrix Γ u = 0) := by
  exact ⟨transfer_matrix_eq_two_cos Γ u,
    transfer_matrix_at_zero Γ,
    transfer_matrix_even_u Γ u,
    lax_phase_additive Γ₁ Γ₂ u,
    transfer_matrix_commutation Γ u v⟩

end InfoGeometry.Canonical.TransferMatrixIntegrabilityCapstone
