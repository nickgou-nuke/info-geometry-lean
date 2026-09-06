import InfoGeometry.Quantum.DensityMatrixPurity

namespace InfoGeometry.Canonical.DensityMatrixPurityCapstone

open InfoGeometry.Quantum.DensityMatrixPurity

theorem capstone_density_matrix_purity_synthesis (S1 S2 S3 : ℝ)
    (h_bloch : S1 ^ 2 + S2 ^ 2 + S3 ^ 2 ≤ 1) (h_pure : purity S1 S2 0 = 1) :
    (Matrix.trace (densityMatrix S1 S2 S3) = 1) ∧
    ((Matrix.trace (densityMatrix S1 S2 S3 * densityMatrix S1 S2 S3)).re = purity S1 S2 S3) ∧
    (purity S1 S2 S3 ≤ 1) ∧
    (purity S1 S2 S3 = 1 ↔ S1 ^ 2 + S2 ^ 2 + S3 ^ 2 = 1) ∧
    (S1 ^ 2 + S2 ^ 2 = 1) :=
  grand_density_matrix_purity_synthesis S1 S2 S3 h_bloch h_pure

end InfoGeometry.Canonical.DensityMatrixPurityCapstone
