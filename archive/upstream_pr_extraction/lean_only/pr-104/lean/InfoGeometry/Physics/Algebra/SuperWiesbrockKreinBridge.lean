import Mathlib
import InfoGeometry.Canonical.WiesbrockSUSYPoincareBridge

/-!
# Krein transport for the finite Wiesbrock generator

The canonical owner defines the finite matrix generator
`P_translation = (2 * π)⁻¹ • (Q_M² - Q_N²)`.  This bridge proves that the
ordinary transpose-weighted symmetry of both supercharges passes to that
generator.  No Hilbert-space, positivity, or half-sided modular inclusion is
asserted here.
-/

namespace SuperWiesbrock

open Matrix

variable {n : ℕ}

lemma transpose_sq_mul_eta
    (A eta : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᵀ * eta = eta * A) :
    (A * A)ᵀ * eta = eta * (A * A) := by
  rw [transpose_mul]
  calc
    Aᵀ * Aᵀ * eta = Aᵀ * (Aᵀ * eta) := by rw [mul_assoc]
    _ = Aᵀ * (eta * A) := by rw [h]
    _ = (Aᵀ * eta) * A := by rw [mul_assoc]
    _ = (eta * A) * A := by rw [h]
    _ = eta * (A * A) := by rw [mul_assoc]

theorem P_translation_pseudo_self_adjoint
    (sc : ModularSupercharges n) (eta : Matrix (Fin n) (Fin n) ℂ)
    (hM : sc.Q_Mᵀ * eta = eta * sc.Q_M)
    (hN : sc.Q_Nᵀ * eta = eta * sc.Q_N) :
    (P_translation sc)ᵀ * eta = eta * P_translation sc := by
  have hM_sq := transpose_sq_mul_eta sc.Q_M eta hM
  have hN_sq := transpose_sq_mul_eta sc.Q_N eta hN
  dsimp [P_translation, K_M, K_N]
  rw [transpose_smul, transpose_sub]
  rw [smul_mul_assoc, sub_mul, hM_sq, hN_sq, ← mul_sub,
    ← mul_smul_comm]

end SuperWiesbrock
