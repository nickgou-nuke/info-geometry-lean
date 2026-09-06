import InfoGeometry.Quantum.DensityMatrixPurity

namespace InfoGeometry.Canonical.DensityMatrixPurityCapstone

open InfoGeometry.Quantum.DensityMatrixPurity

/-! Direct density-matrix normalization, purity, and equatorial confinement. -/
theorem capstone_density_matrix_purity_synthesis (S1 S2 S3 : ℝ)
    (h_bloch : S1 ^ 2 + S2 ^ 2 + S3 ^ 2 ≤ 1) (h_pure : purity S1 S2 0 = 1) :
    (Matrix.trace (densityMatrix S1 S2 S3) = 1) ∧
    ((Matrix.trace (densityMatrix S1 S2 S3 * densityMatrix S1 S2 S3)).re =
      purity S1 S2 S3) ∧
    (purity S1 S2 S3 ≤ 1) ∧
    (purity S1 S2 S3 = 1 ↔ S1 ^ 2 + S2 ^ 2 + S3 ^ 2 = 1) ∧
    (S1 ^ 2 + S2 ^ 2 = 1) := by
  exact ⟨densityMatrix_trace S1 S2 S3,
    densityMatrix_purity_eq S1 S2 S3,
    purity_le_one S1 S2 S3 h_bloch,
    purity_eq_one_iff S1 S2 S3,
    densityMatrix_pure_equator_confinement S1 S2 h_pure⟩

end InfoGeometry.Canonical.DensityMatrixPurityCapstone
