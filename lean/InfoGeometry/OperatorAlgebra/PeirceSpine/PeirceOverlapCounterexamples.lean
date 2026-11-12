/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Opposite Peirce corners and vanishing overlap

The proposed three-dimensional witness `E₁₂, E₃₁` has nonzero reverse
product `E₃₂`. A corrected example lives in the full real four-dimensional
matrix algebra: `P = E₁₁ + E₄₄`, `N₊ = E₁₂`, and `N₋ = E₃₄`.
Both corners are nonzero while both round trips vanish. The two seeds are
independent and are not adjoints of one another.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceOverlapCounterexamples

private def e {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ := Matrix.single i j 1

private theorem e_mul {n : ℕ} (i j k l : Fin n) :
    e i j * e k l = if j = k then e i l else 0 := by
  by_cases h : j = k
  · subst k
    simp [e]
  · rw [if_neg h]
    simpa [e] using Matrix.single_mul_single_of_ne (1 : ℝ) i j k h (1 : ℝ)

/-- The original three-dimensional pair has a nonzero reverse product. -/
theorem three_dimensional_pair_overlap :
    (Matrix.single (0 : Fin 3) 1 (1 : ℝ) * Matrix.single 2 0 1 +
      Matrix.single 2 0 1 * Matrix.single 0 1 1) = Matrix.single 2 1 1 := by
  change e (0 : Fin 3) 1 * e 2 0 + e 2 0 * e 0 1 = e 2 1
  simp [e_mul]

/-- In particular the proposed `E₁₂,E₃₁` zero-overlap claim is false. -/
theorem three_dimensional_pair_overlap_ne_zero :
    (Matrix.single (0 : Fin 3) 1 (1 : ℝ) * Matrix.single 2 0 1 +
      Matrix.single 2 0 1 * Matrix.single 0 1 1) ≠ 0 := by
  rw [three_dimensional_pair_overlap]
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 1) h
  norm_num [Matrix.single] at hentry

/-- The original pair still defeats a nonzero double-commutator multiplier:
its coupling is nonzero, but its product with the odd generator vanishes and
the sum of the corners is cube-zero. These are genuine Peirce corners of the
stated three-dimensional cut. -/
theorem three_dimensional_nonzero_coupling_zero_multiplier :
    let P : Matrix (Fin 3) (Fin 3) ℝ := Matrix.single 0 0 1
    let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.single 0 1 1
    let C : Matrix (Fin 3) (Fin 3) ℝ := Matrix.single 2 0 1
    genV P A C ≠ 0 ∧ genV P A C * genJ P A C = 0 ∧ (genPhi P A C) ^ 3 = 0 := by
  change genV (e (0 : Fin 3) 0) (e 0 1) (e 2 0) ≠ 0 ∧
    genV (e 0 0) (e 0 1) (e 2 0) * genJ (e 0 0) (e 0 1) (e 2 0) = 0 ∧
    genPhi (e 0 0) (e 0 1) (e 2 0) ^ 3 = 0
  have hup : conePlus (e (0 : Fin 3) 0) (e 0 1) = e 0 1 := by
    simp [conePlus, mul_sub, e_mul]
  have hdown : coneMinus (e (0 : Fin 3) 0) (e 2 0) = e 2 0 := by
    simp [coneMinus, sub_mul, e_mul]
  simp only [genV, genJ, genPhi, anticomm, hup, hdown]
  refine ⟨three_dimensional_pair_overlap_ne_zero, ?_, ?_⟩
  · simp [mul_add, add_mul, mul_sub, sub_mul, e_mul]
  · simp [pow_succ, mul_add, add_mul, e_mul]

/-- The cut retains the first and fourth coordinate directions. -/
def independentCut : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.single 0 0 1 + Matrix.single 3 3 1

/-- A transfer from the second direction to the first. -/
def independentUpper : Matrix (Fin 4) (Fin 4) ℝ := Matrix.single 0 1 1

/-- A transfer from the fourth direction to the third. -/
def independentLower : Matrix (Fin 4) (Fin 4) ℝ := Matrix.single 2 3 1

theorem independentCut_idempotent : independentCut * independentCut = independentCut := by
  change (e (0 : Fin 4) 0 + e 3 3) * (e 0 0 + e 3 3) = e 0 0 + e 3 3
  simp [mul_add, add_mul, e_mul]

theorem independentUpper_corner :
    conePlus independentCut independentUpper = independentUpper := by
  change (e (0 : Fin 4) 0 + e 3 3) * e 0 1 * (1 - (e 0 0 + e 3 3)) = e 0 1
  simp [mul_sub, mul_add, add_mul, e_mul]

theorem independentLower_corner :
    coneMinus independentCut independentLower = independentLower := by
  change (1 - (e (0 : Fin 4) 0 + e 3 3)) * e 2 3 * (e 0 0 + e 3 3) = e 2 3
  simp [sub_mul, mul_add, add_mul, e_mul]

theorem independentUpper_ne_zero : independentUpper ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
  norm_num [independentUpper, Matrix.single] at hentry

theorem independentLower_ne_zero : independentLower ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 3) h
  norm_num [independentLower, Matrix.single] at hentry

/-- The forward round trip vanishes for the independent pair. -/
theorem independentUpper_mul_lower : independentUpper * independentLower = 0 := by
  change e (0 : Fin 4) 1 * e 2 3 = 0
  simp [e_mul]

/-- The reverse round trip vanishes separately. -/
theorem independentLower_mul_upper : independentLower * independentUpper = 0 := by
  change e (2 : Fin 4) 3 * e 0 1 = 0
  simp [e_mul]

/-- Actual opposite nonzero Peirce corners can have zero coupling when the
two seeds are independent. -/
theorem independent_genV_eq_zero :
    genV independentCut independentUpper independentLower = 0 := by
  rw [genV, anticomm, independentUpper_corner, independentLower_corner,
    independentUpper_mul_lower, independentLower_mul_upper, add_zero]

/-- The cut and upper seed fail to commute, despite zero coupling. -/
theorem independent_cut_upper_not_commute :
    ¬ Commute independentCut independentUpper := by
  intro h
  have hproduct : independentCut * independentUpper = independentUpper := by
    change (e (0 : Fin 4) 0 + e 3 3) * e 0 1 = e 0 1
    simp [add_mul, e_mul]
  have hreverse : independentUpper * independentCut = 0 := by
    change e (0 : Fin 4) 1 * (e 0 0 + e 3 3) = 0
    simp [mul_add, e_mul]
  exact independentUpper_ne_zero (hproduct.symm.trans (h.eq.trans hreverse))

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceOverlapCounterexamples
