import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import proofs.SplitOctonionSL2MatrixBridge

open Quaternion
open Matrix
open SplitOctonion
open SplitOctonionSL2MatrixBridge

namespace SplitOctonionNilpotentExp

instance : Zero SplitOct where zero := ⟨0, 0⟩
@[simp] lemma zero_def : (0 : SplitOct) = ⟨0, 0⟩ := rfl

theorem E_sq_zero : E * E = 0 := by
  ext1 <;> ext1 <;> simp [E, u, ell, smul_def, add_def, mul_def, star, zero_def] <;> ring

theorem F_sq_zero : F * F = 0 := by
  ext1 <;> ext1 <;> simp [F, u, ell, smul_def, sub_def, mul_def, star, zero_def] <;> ring

noncomputable def expE (a : ℝ) : SplitOct := 1 + a • E

noncomputable def expF (b : ℝ) : SplitOct := 1 + b • F

theorem expE_def (a : ℝ) : expE a = 1 + a • E := rfl
theorem expF_def (b : ℝ) : expF b = 1 + b • F := rfl

theorem expE_mul_expE (a b : ℝ) : expE a * expE b = expE (a + b) := by
  ext1 <;> ext1 <;> simp [expE, E, u, ell, smul_def, add_def, mul_def, star] <;> ring

theorem expF_mul_expF (a b : ℝ) : expF a * expF b = expF (a + b) := by
  ext1 <;> ext1 <;> simp [expF, F, u, ell, smul_def, add_def, sub_def, mul_def, star] <;> ring

theorem bracket_E_F : bracket E F = H := by
  ext1 <;> ext1 <;> simp [bracket, E, F, H, u, ell, smul_def, add_def, sub_def, mul_def, star] <;> ring

theorem bracket_H_E : bracket H E = (2 : ℝ) • E := by
  ext1 <;> ext1 <;> simp [bracket, H, E, u, ell, smul_def, add_def, sub_def, mul_def, star] <;> ring

theorem bracket_H_F : bracket H F = (-2 : ℝ) • F := by
  ext1 <;> ext1 <;> simp [bracket, H, F, u, ell, smul_def, add_def, sub_def, mul_def, star] <;> ring

end SplitOctonionNilpotentExp
