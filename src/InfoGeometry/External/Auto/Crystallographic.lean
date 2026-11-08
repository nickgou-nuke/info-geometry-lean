import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Real.Basic

open Real

/-- 
  The Crystallographic Restriction Theorem (Trace Form)
  
  In a 2D discrete periodic lattice (wallpaper group), the rotation matrices must 
  have integer entries in some basis, meaning their trace is an integer.
  Since the trace of a 2D rotation matrix is 2 * cos(θ), it must hold that 2 * cos(θ) ∈ ℤ.
  
  Because -1 ≤ cos(θ) ≤ 1, this restricts 2 * cos(θ) to the discrete set {-2, -1, 0, 1, 2}.
  This fundamentally forbids 5-fold (pentagonal) or 7-fold symmetries in commutative 
  periodic classical geometry.
-/
lemma crystallographic_restriction (θ : ℝ) (k : ℤ) (h_trace : 2 * cos θ = (k : ℝ)) : 
  k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2 := by
  have h_cos_ge : -1 ≤ cos θ := neg_one_le_cos θ
  have h_cos_le : cos θ ≤ 1 := cos_le_one θ
  
  have hk_ge : (-2 : ℝ) ≤ (k : ℝ) := by
    calc (-2 : ℝ) = 2 * (-1) := by ring
      _ ≤ 2 * cos θ := mul_le_mul_of_nonneg_left h_cos_ge (by norm_num)
      _ = (k : ℝ) := h_trace
      
  have hk_le : (k : ℝ) ≤ (2 : ℝ) := by
    calc (k : ℝ) = 2 * cos θ := h_trace.symm
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left h_cos_le (by norm_num)
      _ = (2 : ℝ) := by ring

  have h_int_ge : -2 ≤ k := by exact_mod_cast hk_ge
  have h_int_le : k ≤ 2 := by exact_mod_cast hk_le
  
  omega
