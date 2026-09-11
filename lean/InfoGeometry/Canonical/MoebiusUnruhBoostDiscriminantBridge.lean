import InfoGeometry.Canonical.MoebiusDiscriminantBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential

namespace InfoGeometry.Canonical

/-- **Теорема**: Мебиусова Дискриминанта на Лоренцов Буст Δ = 4 sinh²(η/2).
    Доказва, че за всеки Унру буст с бързина η, дискриминантата се изразява чрез хиперболичния синус! -/
theorem moebius_discriminant_unruh_boost (eta : ℝ) :
    moebiusDiscriminant (Real.exp (eta / 2) : ℂ) (Real.exp (-eta / 2) : ℂ) = (4 * (Real.sinh (eta / 2))^2 : ℂ) := by
  dsimp [moebiusDiscriminant]
  have h_cosh : (Real.exp (eta / 2) : ℂ) + (Real.exp (-eta / 2) : ℂ) = 2 * Complex.cosh ↑(eta / 2) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp]
    push_cast
    dsimp [Complex.cosh]
    ring_nf
  rw [h_cosh]
  have h_sub : (Complex.cosh ↑(eta / 2))^2 - 1 = (Complex.sinh ↑(eta / 2))^2 := by
    have h := Complex.cosh_sq_sub_sinh_sq (↑(eta / 2) : ℂ)
    calc (Complex.cosh ↑(eta / 2))^2 - 1
        = (Complex.cosh ↑(eta / 2))^2 - (Complex.cosh ↑(eta / 2) ^ 2 - Complex.sinh ↑(eta / 2) ^ 2) := by rw [h]
      _ = Complex.sinh ↑(eta / 2) ^ 2 := by ring
  calc (2 * Complex.cosh ↑(eta / 2))^2 - 4
      = 4 * ((Complex.cosh ↑(eta / 2))^2 - 1) := by ring
    _ = 4 * (Complex.sinh ↑(eta / 2))^2 := by rw [h_sub]
    _ = 4 * (Real.sinh (eta / 2) : ℂ)^2 := by rw [Complex.ofReal_sinh]

/-- **Master Synthesis**: Мебиусова Дискриминанта & Унру Буст Synthesis -/
theorem master_moebius_unruh_boost_synthesis (eta : ℝ) :
    moebiusDiscriminant (Real.exp (eta / 2) : ℂ) (Real.exp (-eta / 2) : ℂ) = (4 * (Real.sinh (eta / 2))^2 : ℂ) :=
  by exact moebius_discriminant_unruh_boost eta

end InfoGeometry.Canonical
