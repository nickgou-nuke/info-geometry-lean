import InfoGeometry.External.Auto.PaperwallHolographicSUSY

/-!
# Paperwall Cuntz/glide SUSY construction

Repaired external file by integrating it with the active
`PaperwallHolographicSUSY` algebraic theorems.
-/

noncomputable section

namespace PaperwallSUSY

variable {R : Type*} [Ring R]

/-- Consolidated paperwall SUSY theorem. -/
theorem paperwall_susy_integrated (c cdag G Ginv : R)
    (c_sq : c * c = 0)
    (c_comm_G : c * G = G * c)
    (fermion_anticomm : c * cdag + cdag * c = 1)
    (G_right_inv : G * Ginv = 1)
    (even_covariant : Ginv * (cdag * c) * G = cdag * c) :
    PaperwallHolographicSUSY.supercharge c G * PaperwallHolographicSUSY.supercharge c G = 0 ∧
    PaperwallHolographicSUSY.susyHamiltonian c cdag G Ginv = 1 := by
  constructor
  · unfold PaperwallHolographicSUSY.supercharge
    calc
      (c * G) * (c * G) = c * (G * c) * G := by noncomm_ring
      _ = c * (c * G) * G := by rw [← c_comm_G]
      _ = (c * c) * (G * G) := by noncomm_ring
      _ = 0 := by rw [c_sq, zero_mul]
  · unfold PaperwallHolographicSUSY.susyHamiltonian PaperwallHolographicSUSY.supercharge
      PaperwallHolographicSUSY.superchargeDag
    calc
      (c * G) * (Ginv * cdag) + (Ginv * cdag) * (c * G)
          = c * (G * Ginv) * cdag + Ginv * (cdag * c) * G := by noncomm_ring
      _ = c * 1 * cdag + cdag * c := by rw [G_right_inv, even_covariant]
      _ = c * cdag + cdag * c := by rw [mul_one]
      _ = 1 := fermion_anticomm

end PaperwallSUSY
