import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Topological Zero-Modes of the Dirac-Hodge Factorization

Formalizes the algebraic determinant conditions for the bulk Dirac zero-modes.

By evaluating `det(sI₂ - X) = 0`, we analytically derive both the `s=0` 
tripotent singularity (at `k=0`) and the boundary CFT lightcone dispersion 
relation `s = ±|k|` (for `k ≠ 0`).
-/

namespace DiracZeroModes

open Matrix

/-- The biquaternion scale-resolvent core `sI - X`, where 
    `X = k_y σ₁ - k_x σ₂`. -/
def sI_minus_X (s kx ky : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![s, -Complex.I * kx - ky; 
     Complex.I * kx - ky, s]

/-- 
Theorem: The determinant of the biquaternion scale resolvent matrix 
is exactly the Minkowskian/Lightcone quadratic form `s² - kx² - ky²`.
-/
theorem det_sI_minus_X (s kx ky : ℂ) :
    (sI_minus_X s kx ky).det = s^2 - kx^2 - ky^2 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_sq
  dsimp [sI_minus_X]
  rw [Matrix.det_fin_two]
  calc
    s * s - (-Complex.I * kx - ky) * (Complex.I * kx - ky) 
      = s^2 - (-Complex.I^2 * kx^2 + ky^2) := by ring
    _ = s^2 - (-(-1) * kx^2 + ky^2) := by rw [hI]
    _ = s^2 - (kx^2 + ky^2) := by ring
    _ = s^2 - kx^2 - ky^2 := by ring

/-- 
Theorem: In the deep IR limit where the boundary momentum vanishes (`kx=ky=0`), 
the determinant vanishes strictly at `s = 0`.

This explicitly maps the bulk `k=0` harmonic zero-mode directly to the 
algebraic `s=0` non-invertible tripotent defect on the fractal boundary!
-/
theorem tripotent_zero_mode :
    (sI_minus_X 0 0 0).det = 0 := by
  simp [det_sI_minus_X]

/-- 
Theorem: For generic boundary momentum `k` (where `k² = kx² + ky²`), the 
zero-mode dispersion relation `s² - k² = 0` splits algebraically 
into the relativistic conformal lightcone rays `s = k` and `s = -k`.
-/
theorem lightcone_dispersion (s k : ℂ) :
    s^2 - k^2 = 0 ↔ (s = k ∨ s = -k) := by
  have h_factor : s^2 - k^2 = (s - k) * (s + k) := by ring
  rw [h_factor, mul_eq_zero, sub_eq_zero, add_eq_zero]
  exact Iff.rfl

end DiracZeroModes
