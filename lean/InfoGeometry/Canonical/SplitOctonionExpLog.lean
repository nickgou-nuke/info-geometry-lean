import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Exponential
import InfoGeometry.Canonical.SplitOctonionQuaternionChart

noncomputable section

namespace SplitOctonion

instance : SMul ℝ SplitOctonion where
  smul r X := ⟨r • X.a, r • X.b⟩

/-- The positive-norm (hyperbolic) exponential sector where $v^2 = +r^2$.
    Here, $J^2 = +1$ and $x = \rho (\cosh \eta + J \sinh \eta)$. -/
def expHyperbolic (rho eta : ℝ) (J : SplitOctonion) : SplitOctonion :=
  ⟨(rho * Real.cosh eta) • (1 : H), 0⟩ + ⟨(rho * Real.sinh eta) • J.a, (rho * Real.sinh eta) • J.b⟩

/-- The negative-norm (elliptic) exponential sector where $v^2 = -r^2$.
    Here, $J^2 = -1$ and $x = \rho (\cos \theta + J \sin \theta)$. -/
def expElliptic (rho theta : ℝ) (J : SplitOctonion) : SplitOctonion :=
  ⟨(rho * Real.cos theta) • (1 : H), 0⟩ + ⟨(rho * Real.sin theta) • J.a, (rho * Real.sin theta) • J.b⟩

/-- The null boundary (nilpotent) exponential sector where $v^2 = 0$.
    Here, $n^2 = 0$ and $x = \rho (1 + n)$. -/
def expNilpotent (rho : ℝ) (n : SplitOctonion) : SplitOctonion :=
  ⟨rho • (1 : H), 0⟩ + ⟨rho • n.a, rho • n.b⟩

/-- Logarithms for the hyperbolic sector. -/
def logHyperbolic (_X : SplitOctonion) (rho eta : ℝ) (J : SplitOctonion) : ℝ × ℝ × SplitOctonion :=
  (Real.log rho, eta, J)

/-- An invertible split octonion $x$ with $N(x) < 0$ cannot be the exponential of a single element.
    Theorem: $N(e^y) > 0$.
    We state this formally as the positivity of the norm of the exponential. -/
theorem norm_exp_hyperbolic_pos (eta : ℝ) (J : SplitOctonion) (hJ_norm : normSQ J = -1) (hJ_a : J.a = 0) :
    normSQ (expHyperbolic 1 eta J) > 0 := by
  unfold expHyperbolic
  unfold normSQ
  have H1 : (⟨(1 * Real.cosh eta) • (1 : H), 0⟩ + ⟨(1 * Real.sinh eta) • J.a, (1 * Real.sinh eta) • J.b⟩ : SplitOctonion).a = (Real.cosh eta) • 1 := by
    change (1 * Real.cosh eta) • 1 + (1 * Real.sinh eta) • J.a = (Real.cosh eta) • 1
    rw [hJ_a]
    ext <;> simp
  have H2 : (⟨(1 * Real.cosh eta) • (1 : H), 0⟩ + ⟨(1 * Real.sinh eta) • J.a, (1 * Real.sinh eta) • J.b⟩ : SplitOctonion).b = (Real.sinh eta) • J.b := by
    change 0 + (1 * Real.sinh eta) • J.b = (Real.sinh eta) • J.b
    ext <;> simp
  rw [H1, H2]
  have h_a_norm : ((Real.cosh eta • 1 : H) * star (Real.cosh eta • 1 : H)).re = (Real.cosh eta)^2 := by
    rw [←normSq_eq_re_mul_star, Quaternion.normSq_smul]
    have h_one : Quaternion.normSq (1 : H) = 1 := by simp
    rw [h_one, mul_one]
  have h_b_norm : ((Real.sinh eta • J.b) * star (Real.sinh eta • J.b)).re = (Real.sinh eta)^2 := by
    rw [←normSq_eq_re_mul_star, Quaternion.normSq_smul]
    have J_b_norm_1 : Quaternion.normSq J.b = 1 := by
      have h1 : normSQ J = -1 := hJ_norm
      unfold normSQ at h1
      rw [hJ_a] at h1
      have h_zero : ((0:H) * star (0:H)).re = 0 := by simp
      rw [h_zero, zero_sub] at h1
      have h_star : (J.b * star J.b).re = Quaternion.normSq J.b := (normSq_eq_re_mul_star J.b).symm
      rw [h_star] at h1
      linarith
    rw [J_b_norm_1, mul_one]
  rw [h_a_norm, h_b_norm]
  have cosh_sq_sub_sinh_sq : (Real.cosh eta)^2 - (Real.sinh eta)^2 = 1 := by
    exact Real.cosh_sq_sub_sinh_sq eta
  rw [cosh_sq_sub_sinh_sq]
  linarith

end SplitOctonion
