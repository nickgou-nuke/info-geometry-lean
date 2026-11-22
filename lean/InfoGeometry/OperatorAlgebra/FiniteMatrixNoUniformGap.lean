/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

/-!
# A matrix witness separating pointwise positivity from uniform coercivity

The upper-triangular matrices below are non-diagonal operators in the full
`2 × 2` matrix algebra. Each member is injective, hence has strictly positive
output energy on every nonzero vector. Across the family, however, a fixed
vector has output energy tending to zero. This is a concrete matrix witness
that pointwise positivity does not supply a uniform lower bound.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteMatrixNoUniformGap

abbrev Vec := Fin 2 → ℝ
abbrev Op := Matrix (Fin 2) (Fin 2) ℝ

/-- A non-diagonal matrix family with a vanishing lower-right coefficient. -/
noncomputable def triangularApproximation (n : ℕ) : Op := fun i j =>
  if i = 0 then 1 else if j = 1 then ((n : ℝ) + 1)⁻¹ else 0

/-- The fixed vector witnessing failure of uniform coercivity. -/
def testVector : Vec := ![-1, 1]

/-- The coordinate quadratic form on this finite-dimensional vector carrier. -/
def squaredCoordinateNorm (v : Vec) : ℝ := (v 0) ^ 2 + (v 1) ^ 2

/-- Output energy of the actual matrix action. -/
noncomputable def operatorEnergy (n : ℕ) (v : Vec) : ℝ :=
  squaredCoordinateNorm ((triangularApproximation n).mulVec v)

@[simp]
theorem triangularApproximation_mulVec (n : ℕ) (v : Vec) :
    (triangularApproximation n).mulVec v =
      ![v 0 + v 1, ((n : ℝ) + 1)⁻¹ * v 1] := by
  ext i
  fin_cases i <;>
    simp [triangularApproximation, Matrix.mulVec]

/-- Each matrix in the family is injective: its two output coordinates
recover the input coordinates in reverse order. -/
theorem triangularApproximation_mulVec_injective (n : ℕ) :
    Function.Injective (fun v : Vec => (triangularApproximation n).mulVec v) := by
  intro v w h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  change ((triangularApproximation n).mulVec v) 0 =
    ((triangularApproximation n).mulVec w) 0 at h₀
  change ((triangularApproximation n).mulVec v) 1 =
    ((triangularApproximation n).mulVec w) 1 at h₁
  rw [triangularApproximation_mulVec, triangularApproximation_mulVec] at h₀ h₁
  have hsecond : v 1 = w 1 := by
    have hcoeff : ((n : ℝ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    have hmul : ((n : ℝ) + 1)⁻¹ * v 1 = ((n : ℝ) + 1)⁻¹ * w 1 := by
      simpa using h₁
    exact mul_left_cancel₀ hcoeff hmul
  funext i
  fin_cases i
  · have hfirst : v 0 + v 1 = w 0 + w 1 := by simpa using h₀
    have hfirst' : v 0 + v 1 = w 0 + v 1 := by simpa [hsecond] using hfirst
    exact add_right_cancel hfirst'
  · simpa using hsecond

private theorem squaredCoordinateNorm_pos_of_ne_zero {v : Vec} (hv : v ≠ 0) :
    0 < squaredCoordinateNorm v := by
  have hcoord : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i <;> simp [h]
  rcases hcoord with h₀ | h₁
  · unfold squaredCoordinateNorm
    nlinarith [sq_pos_of_ne_zero h₀, sq_nonneg (v 1)]
  · unfold squaredCoordinateNorm
    nlinarith [sq_nonneg (v 0), sq_pos_of_ne_zero h₁]

/-- Every individual matrix has a strictly positive quadratic form away from
zero. The lower bound may depend on `n`. -/
theorem operatorEnergy_pos (n : ℕ) {v : Vec} (hv : v ≠ 0) :
    0 < operatorEnergy n v := by
  apply squaredCoordinateNorm_pos_of_ne_zero
  intro hzero
  apply hv
  apply triangularApproximation_mulVec_injective n
  simpa using hzero

@[simp]
theorem squaredCoordinateNorm_testVector : squaredCoordinateNorm testVector = 2 := by
  norm_num [squaredCoordinateNorm, testVector]

/-- The witness energy is exactly the square of the shrinking coefficient. -/
theorem operatorEnergy_testVector (n : ℕ) :
    operatorEnergy n testVector = (((n : ℝ) + 1)⁻¹) ^ 2 := by
  rw [operatorEnergy, triangularApproximation_mulVec]
  norm_num [squaredCoordinateNorm, testVector]

/-- Although the lower bound is not uniform in `n`, every individual matrix
has an explicit coercivity constant.  This is the quantitative replacement
for the failed uniform-gap claim, on the same non-diagonal matrix family. -/
theorem operatorEnergy_explicit_lower_bound (n : ℕ) (v : Vec) :
    ((((n : ℝ) + 1)⁻¹) ^ 2 / 4) * squaredCoordinateNorm v ≤
      operatorEnergy n v := by
  let e : ℝ := ((n : ℝ) + 1)⁻¹
  have hepos : 0 < e := by
    dsimp [e]
    positivity
  have he_le : e ≤ 1 := by
    dsimp [e]
    have hn : 1 ≤ (n : ℝ) + 1 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact (inv_le_one₀ (by positivity)).2 hn
  have hq_nonneg : 0 ≤ e ^ 2 := sq_nonneg e
  have hq_le : e ^ 2 ≤ 1 := by nlinarith
  have hprod : 0 ≤ e ^ 2 * ((v 0 + v 1) + v 1) ^ 2 :=
    mul_nonneg hq_nonneg (sq_nonneg ((v 0 + v 1) + v 1))
  have hremain : 0 ≤ (4 - 2 * e ^ 2) * (v 0 + v 1) ^ 2 +
      e ^ 2 * (v 1) ^ 2 := by
    apply add_nonneg
    · exact mul_nonneg (by nlinarith [hq_le]) (sq_nonneg (v 0 + v 1))
    · exact mul_nonneg hq_nonneg (sq_nonneg (v 1))
  change (e ^ 2 / 4) * squaredCoordinateNorm v ≤
    squaredCoordinateNorm ((triangularApproximation n).mulVec v)
  rw [triangularApproximation_mulVec]
  simp only [squaredCoordinateNorm, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcoordinate : v 0 = (v 0 + v 1) - v 1 := by ring
  nlinarith [hprod, hremain, sq_nonneg (v 1)]

/-- No single positive constant lower-bounds this pointwise-positive matrix
family. This is the concrete approximate-zero-mode obstruction needed to
separate pointwise curvature positivity from a uniform operator gap. -/
theorem no_uniform_quadratic_coercivity :
    ¬ ∃ gap : ℝ, 0 < gap ∧
      ∀ n : ℕ, ∀ v : Vec,
        gap ^ 2 * squaredCoordinateNorm v ≤ operatorEnergy n v := by
  rintro ⟨gap, hgap, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt gap⁻¹
  have hmul : 1 < gap * (n : ℝ) := by
    have h := mul_lt_mul_of_pos_left hn hgap
    rw [mul_inv_cancel₀ hgap.ne'] at h
    exact h
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hmul_succ : 1 < gap * ((n : ℝ) + 1) := by
    exact lt_trans hmul (by nlinarith [hgap])
  have hsmall : ((n : ℝ) + 1)⁻¹ < gap := by
    have hdiv : 1 / ((n : ℝ) + 1) < gap :=
      (div_lt_iff₀ hnpos).2 hmul_succ
    simpa [one_div] using hdiv
  have hsmall_sq : (((n : ℝ) + 1)⁻¹) ^ 2 < gap ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hsmall)
      (add_pos (by positivity : 0 < ((n : ℝ) + 1)⁻¹) hgap)
    nlinarith
  have h := hbound n testVector
  rw [squaredCoordinateNorm_testVector, operatorEnergy_testVector] at h
  nlinarith [sq_pos_of_pos hgap]

end InfoGeometry.OperatorAlgebra.FiniteMatrixNoUniformGap
