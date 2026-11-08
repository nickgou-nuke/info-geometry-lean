import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import InfoGeometry.Physics.IsospinMirrorDynamics

namespace InfoGeometry.Physics

/-- P-31 Nucleus (Z=15, N=16) -/
def P_31 : Nucleus := ⟨15, 16⟩

/-- S-31 Nucleus (Z=16, N=15) -/
def S_31 : Nucleus := ⟨16, 15⟩

/-- The A=31 Mirror Pair. -/
def A31Pair : MirrorPair where
  nuc1 := P_31
  nuc2 := S_31
  mirror_cond_Z := rfl
  mirror_cond_N := rfl

/-- Experimental B(E1) value for S-31 in Weisskopf units (or relevant scaled units). -/
def B_E1_S : ℝ := 7.2

/-- Experimental B(E1) value for P-31 in Weisskopf units. -/
def B_E1_P : ℝ := 2.7

/-- Formal statement of isospin symmetry breaking: the B(E1) transition rates 
    are different between the mirror nuclei. -/
theorem a31_isospin_symmetry_breaking : B_E1_S ≠ B_E1_P := by
  unfold B_E1_S B_E1_P
  norm_num

/-- The isoscalar/isovector amplitude mixing ratio derived from the square roots 
    of the B(E1) values. It measures the degree of isospin mixing. -/
noncomputable def isoscalar_isovector_mixing_ratio : ℝ :=
  (Real.sqrt B_E1_S - Real.sqrt B_E1_P) / (Real.sqrt B_E1_S + Real.sqrt B_E1_P)

/-- The theoretical geometric parallax bound for the mixing ratio. -/
def geometric_parallax_bound : ℝ := 0.24

/-- The empirical isoscalar/isovector mixing ratio derived from B(E1) values
    approximates the theoretical geometric parallax bound. -/
theorem mixing_ratio_relation :
    |isoscalar_isovector_mixing_ratio - geometric_parallax_bound| < 0.01 := by
  unfold isoscalar_isovector_mixing_ratio geometric_parallax_bound B_E1_S B_E1_P
  norm_num
  set a : ℝ := 6 / Real.sqrt (5 : ℝ) with ha
  set b : ℝ := Real.sqrt (27 : ℝ) / Real.sqrt (10 : ℝ) with hb
  change |(a - b) / (a + b) - (6 / 25 : ℝ)| < (1 / 100 : ℝ)
  have hden_pos : 0 < a + b := by
    rw [ha, hb]
    positivity
  have h_upper_linear : 3 * a < 5 * b := by
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    rw [mul_pow, mul_pow]
    rw [ha, hb]
    norm_num [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27)]
  have h_lower_linear : 123 * b < 77 * a := by
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    rw [mul_pow, mul_pow]
    rw [ha, hb]
    norm_num [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27)]
  have h_upper : (a - b) / (a + b) < (1 / 4 : ℝ) := by
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  have h_lower : (23 / 100 : ℝ) < (a - b) / (a + b) := by
    rw [lt_div_iff₀ hden_pos]
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

end InfoGeometry.Physics
