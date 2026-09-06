import Mathlib

/-!
# Dirac-Hodge operator in the Fourier--Mellin domain

Finite `2x2` matrix anchors for the Fourier--Mellin Dirac symbol and its
factorization through a biquaternion scale-resolvent core.
-/

namespace DiracFourierMellin

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The transformed Dirac symbol in Mellin/Fourier variables. -/
def D_FM (s kx ky : ℂ) : M2C :=
  !![-s, I * kx + ky; I * kx - ky, s]

/-- The biquaternion scale-resolvent core `sI-X`. -/
def sI_minus_X (s kx ky : ℂ) : M2C :=
  !![s, -I * kx - ky; I * kx - ky, s]

/-- Radial Pauli matrix `sigma3`. -/
def sigma3 : M2C :=
  !![1, 0; 0, -1]

/-- The transformed Dirac symbol squares to `(s^2-kx^2-ky^2)I`. -/
theorem dirac_sq_laplacian (s kx ky : ℂ) :
    D_FM s kx ky * D_FM s kx ky =
      (s ^ 2 - kx ^ 2 - ky ^ 2) • (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [D_FM, Matrix.mul_apply, Matrix.smul_apply] <;>
    ring_nf <;>
    try rw [Complex.I_sq] <;>
    ring

/-- `D_FM = -sigma3 (sI-X)`, connecting the Dirac symbol to the resolvent core. -/
theorem dirac_factors_resolvent (s kx ky : ℂ) :
    D_FM s kx ky = -sigma3 * sI_minus_X s kx ky := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [D_FM, sI_minus_X, sigma3, Matrix.mul_apply] <;>
    ring_nf

end DiracFourierMellin
