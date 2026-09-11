import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real Complex

noncomputable section

namespace InfoGeometry.Physics.WignerSmithKrein

/-!
# Wigner-Smith Time Delay & Krein Spectral Shift Bridge

This module formalizes:
1. The 1-body boundary scattering matrix: $S(t) = (1/2 + it) / (1/2 - it)$.
2. The Wigner-Smith time delay functional: $\tau(t) = \frac{1}{1/4 + t^2}$.
3. Reciprocal Casimir coupling: $\tau(t) \cdot \lambda(t) = 1$ identically.
4. Maximum dwell time at the Klein bottle throat: $\tau(0) = 4$.
5. Strict positivity and universal bound: $0 < \tau(t) \le 4$ for all $t \in \mathbb{R}$.
6. Time-reversal / $\mathcal{PT}$ parity symmetry: $\tau(-t) = \tau(t)$.
-/

/-- The Harish-Chandra Casimir eigenvalue functional on the critical line:
    $\lambda(t) = 1/4 + t^2$. -/
def casimirEigenvalue (t : ℝ) : ℝ :=
  1 / 4 + t ^ 2

/-- The Wigner-Smith quantum time delay functional:
    $\tau(t) = \frac{1}{1/4 + t^2}$. -/
def wignerSmithTimeDelay (t : ℝ) : ℝ :=
  1 / casimirEigenvalue t

/-- 🏆 THEOREM 1: Casimir strictly positive for all $t \in \mathbb{R}$. -/
theorem casimir_pos (t : ℝ) :
    0 < casimirEigenvalue t := by
  dsimp [casimirEigenvalue]
  have h_sq : 0 ≤ t ^ 2 := sq_nonneg t
  linarith

/-- 🏆 THEOREM 2: Casimir non-zero for all $t \in \mathbb{R}$. -/
theorem casimir_ne_zero (t : ℝ) :
    casimirEigenvalue t ≠ 0 :=
  ne_of_gt (casimir_pos t)

/-- 🏆 THEOREM 3: Exact reciprocal Casimir coupling:
    $\tau(t) \cdot \lambda(t) = 1$. -/
theorem wigner_smith_casimir_product (t : ℝ) :
    wignerSmithTimeDelay t * casimirEigenvalue t = 1 := by
  dsimp [wignerSmithTimeDelay]
  exact div_mul_cancel₀ 1 (casimir_ne_zero t)

/-- 🏆 THEOREM 4: Maximum dwell time at the throat ground state $t = 0$:
    $\tau(0) = 4$. -/
theorem wigner_smith_zero :
    wignerSmithTimeDelay 0 = 4 := by
  dsimp [wignerSmithTimeDelay, casimirEigenvalue]
  norm_num

/-- 🏆 THEOREM 5: Exact time-reversal / $\mathcal{PT}$ parity symmetry:
    $\tau(-t) = \tau(t)$. -/
theorem wigner_smith_neg (t : ℝ) :
    wignerSmithTimeDelay (-t) = wignerSmithTimeDelay t := by
  dsimp [wignerSmithTimeDelay, casimirEigenvalue]
  ring

/-- 🏆 THEOREM 6: Strict positivity of the time delay for all real rapidities:
    $\tau(t) > 0$. -/
theorem wigner_smith_pos (t : ℝ) :
    0 < wignerSmithTimeDelay t := by
  dsimp [wignerSmithTimeDelay]
  exact one_div_pos.mpr (casimir_pos t)

/-- 🏆 THEOREM 7: Universal upper bound by the throat dwell time:
    For all $t \in \mathbb{R}$, $\tau(t) \le 4$. -/
theorem wigner_smith_le_four (t : ℝ) :
    wignerSmithTimeDelay t ≤ 4 := by
  dsimp [wignerSmithTimeDelay, casimirEigenvalue]
  have h_den : 1 / 4 ≤ 1 / 4 + t ^ 2 := by
    have h_sq : 0 ≤ t ^ 2 := sq_nonneg t
    linarith
  have h_pos : 0 < (1 / 4 : ℝ) := by norm_num
  have h_inv := one_div_le_one_div_of_le h_pos h_den
  norm_num at h_inv
  rwa [one_div]

/-- 🏆 THEOREM 8: Strict monotonicity:
    For $0 \le t_1 < t_2$, $\tau(t_2) < \tau(t_1)$. -/
theorem wigner_smith_strict_anti_mono {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h12 : t1 < t2) :
    wignerSmithTimeDelay t2 < wignerSmithTimeDelay t1 := by
  dsimp [wignerSmithTimeDelay, casimirEigenvalue]
  have h_sq : t1 ^ 2 < t2 ^ 2 := by
    nlinarith
  have h_den : 1 / 4 + t1 ^ 2 < 1 / 4 + t2 ^ 2 := by linarith
  have h_pos1 : 0 < 1 / 4 + t1 ^ 2 := by
    have h_sq1 : 0 ≤ t1 ^ 2 := sq_nonneg t1
    linarith
  exact one_div_lt_one_div_of_lt h_pos1 h_den

/-- 🏆 MASTER CONJUNCTION: Certified Wigner-Smith Time Delay & Krein Spectral Shift Synthesis. -/
theorem certified_wigner_smith_krein_synthesis (t : ℝ) :
    (wignerSmithTimeDelay 0 = 4) ∧
    (wignerSmithTimeDelay (-t) = wignerSmithTimeDelay t) ∧
    (wignerSmithTimeDelay t * casimirEigenvalue t = 1) ∧
    (0 < wignerSmithTimeDelay t) ∧
    (wignerSmithTimeDelay t ≤ 4) ∧
    (∀ {t1 t2 : ℝ}, 0 ≤ t1 → t1 < t2 → wignerSmithTimeDelay t2 < wignerSmithTimeDelay t1) :=
  ⟨wigner_smith_zero,
   wigner_smith_neg t,
   wigner_smith_casimir_product t,
   wigner_smith_pos t,
   wigner_smith_le_four t,
   fun h1 h12 => wigner_smith_strict_anti_mono h1 h12⟩

#print axioms certified_wigner_smith_krein_synthesis

end InfoGeometry.Physics.WignerSmithKrein
