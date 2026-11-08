import InfoGeometry.External.Auto.DiracResolventZeroModeTripotent
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Dirac zero modes from the Fourier--Mellin resolvent

Repaired external file: determinant, zero-momentum pole, and light-cone factor
statements as direct algebraic theorems.
-/

noncomputable section

namespace DiracZeroModes

abbrev M2C := DiracResolventZeroModeTripotent.M2C

def sI_minus_X (s kx ky : ℂ) : M2C := DiracResolventZeroModeTripotent.sI_minus_X s kx ky

theorem det_sI_minus_X (s kx ky : ℂ) :
    (sI_minus_X s kx ky).det = s ^ 2 - kx ^ 2 - ky ^ 2 :=
  DiracResolventZeroModeTripotent.det_sI_minus_X s kx ky

/-- At zero momentum the resolvent determinant vanishes at `s=0`. -/
theorem tripotent_zero_mode : (sI_minus_X 0 0 0).det = 0 := by
  rw [det_sI_minus_X]
  ring

/-- At zero momentum, the pole is exactly `s=0`. -/
theorem zero_momentum_scale_zero (s : ℂ) :
    (sI_minus_X s 0 0).det = 0 ↔ s = 0 :=
  DiracResolventZeroModeTripotent.zero_momentum_scale_zero s

/-- Algebraic light-cone factorization over `ℂ`. -/
theorem lightcone_dispersion (s k : ℂ) :
    s ^ 2 - k ^ 2 = 0 ↔ (s = k ∨ s = -k) := by
  rw [show s ^ 2 - k ^ 2 = (s - k) * (s + k) by ring]
  rw [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

#check det_sI_minus_X
#check tripotent_zero_mode
#check zero_momentum_scale_zero
#check lightcone_dispersion

end DiracZeroModes
