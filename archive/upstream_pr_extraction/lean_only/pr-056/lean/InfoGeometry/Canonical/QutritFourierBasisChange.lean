import Mathlib
import InfoGeometry.Canonical.SixStateSpectralBridge
import InfoGeometry.Topology.AharonovBohmConcreteVortex

/-!
# Qutrit Fourier basis change

The columns below are the concrete (unnormalized) Fourier eigenvectors already
used by the qutrit spectral owner.  This file packages them as a matrix and
proves the shift--clock intertwining directly.  No unitary normalization is
asserted here; that is a separate normed statement requiring the chosen scalar
normalization.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritFourierBasisChange

open Matrix
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.SixStateSpectralBridge
open InfoGeometry.Topology.Parafermion

abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-- The unnormalized qutrit Fourier matrix, with spectral columns indexed by `b`. -/
def qutritFourierRaw : QutritMatrix :=
  fun a b => (colorEigenvector (omega ^ (b : ℕ))) a

@[simp] theorem qutritFourierRaw_apply (a b : Fin 3) :
    qutritFourierRaw a b = (colorEigenvector (omega ^ (b : ℕ))) a := by
  simp [qutritFourierRaw]

theorem qutritFourierRaw_column_eigen (b : Fin 3) :
    colorShift *ᵥ (fun a => qutritFourierRaw a b) =
      (omega ^ (b : ℕ)) • (fun a => qutritFourierRaw a b) := by
  simpa [qutritFourierRaw] using
    colorEigenvector_shift (omega ^ (b : ℕ)) (by
      calc
        (omega ^ (b : ℕ)) ^ 3 = omega ^ ((b : ℕ) * 3) := by rw [pow_mul]
        _ = omega ^ (3 * (b : ℕ)) := by congr 1; ring
        _ = (omega ^ 3) ^ (b : ℕ) := by rw [pow_mul]
        _ = 1 := by rw [omega_cube_eq_one]; simp)

theorem colorShift_mul_qutritFourierRaw :
    colorShift * qutritFourierRaw =
      qutritFourierRaw * colorClock omega := by
  ext i j
  change (colorShift *ᵥ (fun a => qutritFourierRaw a j)) i =
    (qutritFourierRaw * colorClock omega) i j
  have hcol := congrFun (qutritFourierRaw_column_eigen j) i
  rw [hcol]
  fin_cases i <;> fin_cases j <;>
    simp [qutritFourierRaw, colorClock, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two] <;>
    ring

end InfoGeometry.Canonical.QutritFourierBasisChange

end noncomputable section
