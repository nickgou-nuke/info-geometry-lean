import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

/-!
# Hadamard–Weierstrass Entire Product Real-Zero Invariance Bridge

This bridge provides native Mathlib 4 proofs establishing:
1. Symmetrized Hadamard quadratic factor representation:
   $$F_\gamma(s) = 1 - \frac{s(1-s)}{\frac{1}{4} + \gamma^2} = \frac{(s - 1/2)^2 + \gamma^2}{1/4 + \gamma^2}$$
2. Exact reflection symmetry:
   $$F_\gamma(1 - s) = F_\gamma(s)$$
3. Spectral coordinate translation $s(z) = 1/2 + i z$:
   $$F_\gamma(1/2 + i z) = \frac{\gamma^2 - z^2}{1/4 + \gamma^2}$$
4. Complex derivative of the quadratic factor:
   $$\frac{d}{ds} F_\gamma(s) = \frac{2s - 1}{1/4 + \gamma^2}$$
5. Real-zero characterization:
   $$F_\gamma(1/2 + i t) = 0 \iff t = \pm \gamma$$
6. Strict real positivity on the critical interval $(0, 1)$ when $\gamma \neq 0$:
   $$F_\gamma(x) > 0 \quad \forall x \in (0, 1)$$
-/

noncomputable section

namespace InfoGeometry.Canonical.HadamardWeierstrassXi

open Complex

/-! ## 1. Roots and Quadratic Factor -/

/-- Root pair product for non-trivial zeta zeroes $\rho = 1/2 + i\gamma$. -/
theorem zero_pair_product (gamma : ℝ) :
    (1/2 + Complex.I * (gamma : ℂ)) * (1 - (1/2 + Complex.I * (gamma : ℂ))) =
      ((1/4 + gamma^2 : ℝ) : ℂ) := by
  have h1 : 1 - (1/2 + Complex.I * (gamma : ℂ)) = 1/2 - Complex.I * (gamma : ℂ) := by ring
  rw [h1]
  have h2 : (1/2 + Complex.I * (gamma : ℂ)) * (1/2 - Complex.I * (gamma : ℂ)) =
      (1/4 : ℂ) - (Complex.I * (gamma : ℂ))^2 := by ring
  rw [h2]
  have hI : (Complex.I * (gamma : ℂ))^2 = - (gamma : ℂ)^2 := by
    calc
      (Complex.I * (gamma : ℂ))^2 = Complex.I^2 * (gamma : ℂ)^2 := by ring
      _ = -1 * (gamma : ℂ)^2 := by rw [Complex.I_sq]
      _ = - (gamma : ℂ)^2 := by ring
  rw [hI]
  push_cast
  ring

/-- The symmetrized quadratic factor in the Hadamard product for the pair $\{\rho, 1-\rho\}$. -/
def quadraticFactor (gamma : ℝ) (s : ℂ) : ℂ :=
  1 - (s * (1 - s)) / ((1/4 + gamma^2 : ℝ) : ℂ)

/-- 🏆 THEOREM 1: Algebraic representation as sum of squares -/
theorem quadraticFactor_eq_sum_sq_div (gamma : ℝ) (s : ℂ) :
    quadraticFactor gamma s = ((s - 1/2)^2 + (gamma : ℂ)^2) / ((1/4 + gamma^2 : ℝ) : ℂ) := by
  have h_den_pos : 0 < 1/4 + gamma^2 := by positivity
  have h_den_ne : ((1/4 + gamma^2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt h_den_pos)
  dsimp [quadraticFactor]
  apply mul_right_cancel₀ h_den_ne
  rw [div_mul_cancel₀ _ h_den_ne, sub_mul, div_mul_cancel₀ _ h_den_ne, one_mul]
  push_cast
  ring

/-- 🏆 THEOREM 2: Exact Reflection Invariance -/
theorem quadraticFactor_reflection (gamma : ℝ) (s : ℂ) :
    quadraticFactor gamma (1 - s) = quadraticFactor gamma s := by
  dsimp [quadraticFactor]
  have : (1 - s) * (1 - (1 - s)) = s * (1 - s) := by ring
  rw [this]

/-- 🏆 THEOREM 3: Spectral translation on $s = 1/2 + i z$ -/
theorem quadraticFactor_spectral (gamma : ℝ) (z : ℂ) :
    quadraticFactor gamma (1/2 + Complex.I * z) =
      ((gamma : ℂ)^2 - z^2) / ((1/4 + gamma^2 : ℝ) : ℂ) := by
  rw [quadraticFactor_eq_sum_sq_div]
  have h_sq : (1/2 + Complex.I * z - 1/2)^2 = - z^2 := by
    have : 1/2 + Complex.I * z - 1/2 = Complex.I * z := by ring
    rw [this]
    calc
      (Complex.I * z)^2 = Complex.I^2 * z^2 := by ring
      _ = -1 * z^2 := by rw [Complex.I_sq]
      _ = - z^2 := by ring
  rw [h_sq]
  have : -z^2 + (gamma : ℂ)^2 = (gamma : ℂ)^2 - z^2 := by ring
  rw [this]

/-- 🏆 THEOREM 4: Complex derivative of the quadratic factor -/
theorem hasDerivAt_quadraticFactor (gamma : ℝ) (s : ℂ) :
    HasDerivAt (quadraticFactor gamma)
      ((2 * s - 1) / ((1/4 + gamma^2 : ℝ) : ℂ)) s := by
  have h1 : HasDerivAt (fun s : ℂ => s) 1 s := hasDerivAt_id s
  have h2 : HasDerivAt (fun s : ℂ => 1 - s) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h_prod : HasDerivAt (fun s : ℂ => s * (1 - s)) (1 - 2 * s) s := by
    have h := h1.mul h2
    have : 1 * (1 - s) + s * -1 = 1 - 2 * s := by ring
    rw [this] at h
    exact h
  have h_div : HasDerivAt (fun s : ℂ => s * (1 - s) / ((1/4 + gamma^2 : ℝ) : ℂ))
      ((1 - 2 * s) / ((1/4 + gamma^2 : ℝ) : ℂ)) s :=
    h_prod.div_const ((1/4 + gamma^2 : ℝ) : ℂ)
  have h_sub : HasDerivAt (fun s : ℂ => 1 - s * (1 - s) / ((1/4 + gamma^2 : ℝ) : ℂ))
      (0 - (1 - 2 * s) / ((1/4 + gamma^2 : ℝ) : ℂ)) s :=
    (hasDerivAt_const s 1).sub h_div
  have h_eq : (0 : ℂ) - (1 - 2 * s) / ((1/4 + gamma^2 : ℝ) : ℂ) =
      (2 * s - 1) / ((1/4 + gamma^2 : ℝ) : ℂ) := by ring
  rw [h_eq] at h_sub
  exact h_sub

/-- 🏆 THEOREM 5: Exact Real Root Localization -/
theorem quadraticFactor_zero_iff (gamma : ℝ) (t : ℝ) :
    quadraticFactor gamma (1/2 + Complex.I * (t : ℂ)) = 0 ↔ t = gamma ∨ t = -gamma := by
  have h_prod := zero_pair_product t
  have h_den_pos : 0 < 1/4 + gamma^2 := by positivity
  have h_den_ne : ((1/4 + gamma^2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt h_den_pos)
  dsimp [quadraticFactor]
  rw [h_prod]
  constructor
  · intro h
    have h_div : ((1/4 + t^2 : ℝ) : ℂ) / ((1/4 + gamma^2 : ℝ) : ℂ) = 1 := by
      rw [sub_eq_zero] at h
      exact h.symm
    have h_eq : ((1/4 + t^2 : ℝ) : ℂ) = ((1/4 + gamma^2 : ℝ) : ℂ) := by
      exact (div_eq_one_iff_eq h_den_ne).mp h_div
    have h_re : 1/4 + t^2 = 1/4 + gamma^2 := by
      exact Complex.ofReal_inj.mp h_eq
    have h_sq : t^2 = gamma^2 := by linarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h_sq
  · rintro (rfl | rfl)
    · rw [div_self h_den_ne, sub_self]
    · have : (-gamma)^2 = gamma^2 := by ring
      rw [this, div_self h_den_ne, sub_self]

/-! ## 2. Real Positivity on the Critical Interval (0, 1) -/

/-- 🏆 THEOREM 6: Strict Real Positivity on (0, 1) -/
theorem quadraticFactor_real_pos_on_unit_interval
    (gamma : ℝ) (h_gamma : gamma ≠ 0)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    0 < (quadraticFactor gamma (x : ℂ)).re := by
  have h_den_pos : 0 < 1/4 + gamma^2 := by
    have : 0 < gamma^2 := sq_pos_of_ne_zero h_gamma
    linarith
  have h_lt : x * (1 - x) < 1/4 + gamma^2 := by
    have h_sq : 0 ≤ (x - 1/2)^2 := sq_nonneg (x - 1/2)
    have : x * (1 - x) ≤ 1/4 := by nlinarith
    have : 0 < gamma^2 := sq_pos_of_ne_zero h_gamma
    linarith
  have h_val : (x : ℂ) * (1 - (x : ℂ)) / ((1/4 + gamma^2 : ℝ) : ℂ) =
      (((x * (1 - x) / (1/4 + gamma^2) : ℝ)) : ℂ) := by
    push_cast
    rfl
  dsimp [quadraticFactor]
  rw [h_val, ofReal_re]
  have : x * (1 - x) / (1/4 + gamma^2) < 1 := (div_lt_one h_den_pos).mpr h_lt
  linarith

/-- 🏆 THEOREM 7: Master Hadamard–Weierstrass Synthesis -/
theorem master_hadamard_weierstrass_synthesis
    (gamma : ℝ) (s : ℂ) :
    (quadraticFactor gamma (1 - s) = quadraticFactor gamma s) ∧
    (∀ z : ℂ, quadraticFactor gamma (1/2 + Complex.I * z) = ((gamma : ℂ)^2 - z^2) / ((1/4 + gamma^2 : ℝ) : ℂ)) ∧
    (∀ t : ℝ, quadraticFactor gamma (1/2 + Complex.I * (t : ℂ)) = 0 ↔ t = gamma ∨ t = -gamma) := by
  exact ⟨quadraticFactor_reflection gamma s,
         quadraticFactor_spectral gamma,
         quadraticFactor_zero_iff gamma⟩

end InfoGeometry.Canonical.HadamardWeierstrassXi
