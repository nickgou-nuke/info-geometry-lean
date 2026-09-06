import proofs.HillWheelerUniversalProjection

noncomputable section

namespace ItFromBitProjectiveHolographicSynthesis

open HillWheelerUniversalProjection

theorem diagonal_hillWheeler_zero_energy
    (h0 h1 n0 n1 : ℂ) :
    hillWheelerSecular (diag2 h0 h1) (diag2 n0 n1) 0 = h0 * h1 := by
  rw [hillWheelerSecular_diag]
  ring

theorem projector0_left_absorbs :
    projector0 * (projector0 + projector1) = projector0 := by
  rw [projector_partition]
  rw [Matrix.mul_one]

theorem projector1_right_absorbs :
    (projector0 + projector1) * projector1 = projector1 := by
  rw [projector_partition]
  rw [Matrix.one_mul]

end ItFromBitProjectiveHolographicSynthesis

end noncomputable section
