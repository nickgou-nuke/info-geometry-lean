import Mathlib.Tactic

/-!
# Relativistic Minkowski spacetime in biquaternions

Finite matrix certificates for the Pauli/biquaternion encoding of the Minkowski
quadratic form and the determinant preservation of an algebraic `SL(2,ℂ)` boost.
-/

namespace MinkowskiBiquaternion

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The spacetime four-vector matrix `X = t I + x σ₁ + y σ₂ + z σ₃`. -/
def spacetimeMatrix (t x y z : ℂ) : M2C :=
  !![t + z, x - I * y; x + I * y, t - z]

/-- The determinant is exactly the Minkowski interval `t² - x² - y² - z²`. -/
theorem det_spacetime_minkowski (t x y z : ℂ) :
    (spacetimeMatrix t x y z).det = t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [spacetimeMatrix, Matrix.det_fin_two, Complex.I_sq]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Algebraic pure boost matrix, parametrized by `cosh`/`sinh` symbols. -/
def boostMatrix (η_cosh η_sinh : ℂ) : M2C :=
  !![η_cosh, η_sinh; η_sinh, η_cosh]

/-- The boost lies in `SL(2,ℂ)` when `cosh²-sinh²=1`. -/
theorem det_boostMatrix (η_cosh η_sinh : ℂ)
    (hLorentz : η_cosh ^ 2 - η_sinh ^ 2 = 1) :
    (boostMatrix η_cosh η_sinh).det = 1 := by
  simp [boostMatrix, Matrix.det_fin_two]
  ring_nf at hLorentz ⊢
  exact hLorentz

/-- Determinant/Minkowski interval preservation under `X ↦ Λ X Λ` for `det Λ=1`. -/
theorem lorentz_invariance (t x y z η_cosh η_sinh : ℂ)
    (hLorentz : η_cosh ^ 2 - η_sinh ^ 2 = 1) :
    ((boostMatrix η_cosh η_sinh) * (spacetimeMatrix t x y z) *
        (boostMatrix η_cosh η_sinh)).det =
      (spacetimeMatrix t x y z).det := by
  rw [Matrix.det_mul, Matrix.det_mul, det_boostMatrix η_cosh η_sinh hLorentz]
  simp

end MinkowskiBiquaternion
