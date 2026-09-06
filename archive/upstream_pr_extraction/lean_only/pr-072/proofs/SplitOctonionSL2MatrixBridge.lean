import proofs.SplitOctonionSL2Slice
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open SplitOctonion
open SplitOctonionSL2Slice
open Matrix

namespace SplitOctonionSL2MatrixBridge

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def Phi (a b c d : ℝ) : M2R :=
  !![a + c, -b + d; b + d, a - c]

theorem sliceToMatrix_mul (a b c d A B C D : ℝ) :
  Phi a b c d * Phi A B C D =
  Phi
    (a*A - b*B + c*C + d*D)
    (a*B + b*A + d*C - c*D)
    (a*C + c*A + d*B - b*D)
    (a*D + d*A + b*C - c*B) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi, Matrix.mul_apply] <;> ring

theorem sliceToMatrix_injective (a b c d A B C D : ℝ)
  (h : Phi a b c d = Phi A B C D) : a = A ∧ b = B ∧ c = C ∧ d = D := by
  have h00 := congr_fun (congr_fun h 0) 0
  have h01 := congr_fun (congr_fun h 0) 1
  have h10 := congr_fun (congr_fun h 1) 0
  have h11 := congr_fun (congr_fun h 1) 1
  simp [Phi] at h00 h01 h10 h11
  constructor
  · linarith
  · constructor
    · linarith
    · constructor
      · linarith
      · linarith

theorem sliceToMatrix_surjective (M : M2R) :
  ∃ a b c d, Phi a b c d = M := by
  use (M 0 0 + M 1 1) / 2
  use (M 1 0 - M 0 1) / 2
  use (M 0 0 - M 1 1) / 2
  use (M 1 0 + M 0 1) / 2
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi] <;> ring

theorem sliceToMatrix_bracket (a b c d A B C D : ℝ) :
  Phi a b c d * Phi A B C D - Phi A B C D * Phi a b c d =
  Phi 0 (2*d*C - 2*c*D) (2*d*B - 2*b*D) (2*b*C - 2*c*B) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi] <;> ring

noncomputable def E : SplitOct := (1/2 : ℝ) • (u - u * ell)
noncomputable def F : SplitOct := -(1/2 : ℝ) • (u + u * ell)
def H : SplitOct := ell

theorem E_maps_to_mat_E : Phi 0 (1/2) 0 (-1/2) = !![0, -1; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi] <;> ring

theorem F_maps_to_mat_F : Phi 0 (-1/2) 0 (-1/2) = !![0, 0; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi] <;> ring

theorem H_maps_to_mat_H : Phi 0 0 1 0 = !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi] <;> ring

theorem mat_sl2_HE :
  Phi 0 0 1 0 * Phi 0 (1/2) 0 (-1/2) - Phi 0 (1/2) 0 (-1/2) * Phi 0 0 1 0 =
  2 • Phi 0 (1/2) 0 (-1/2) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi, Matrix.mul_apply, sub_apply, smul_apply, Pi.smul_apply] <;> ring

theorem mat_sl2_HF :
  Phi 0 0 1 0 * Phi 0 (-1/2) 0 (-1/2) - Phi 0 (-1/2) 0 (-1/2) * Phi 0 0 1 0 =
  (-2 : ℝ) • Phi 0 (-1/2) 0 (-1/2) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi, Matrix.mul_apply, sub_apply, smul_apply, Pi.smul_apply] <;> ring

theorem mat_sl2_EF :
  Phi 0 (1/2) 0 (-1/2) * Phi 0 (-1/2) 0 (-1/2) - Phi 0 (-1/2) 0 (-1/2) * Phi 0 (1/2) 0 (-1/2) =
  Phi 0 0 1 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi, Matrix.mul_apply, sub_apply] <;> ring

section GaussDecomposition

theorem Phi_exp_aE (a : ℝ) :
    Phi 1 (a/2) 0 (-a/2) = !![1, -a; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi] <;> ring

theorem Phi_exp_bF (b : ℝ) :
    Phi 1 (-b/2) 0 (-b/2) = !![1, 0; -b, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi] <;> ring

theorem Phi_exp_etaH (η : ℝ) :
    Phi (Real.cosh η) 0 (Real.sinh η) 0 = !![Real.exp η, 0; 0, Real.exp (-η)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi]

theorem gauss_cell_decomposition (a η b : ℝ) :
    Phi 1 (a/2) 0 (-a/2) *
    Phi (Real.cosh η) 0 (Real.sinh η) 0 *
    Phi 1 (-b/2) 0 (-b/2) =
    !![Real.exp η + a*b*Real.exp (-η), -a*Real.exp (-η);
       -b*Real.exp (-η), Real.exp (-η)] := by
  rw [Phi_exp_aE, Phi_exp_etaH, Phi_exp_bF]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring

theorem gauss_cell_det_one (a η b : ℝ) :
    Matrix.det (
      !![Real.exp η + a*b*Real.exp (-η), -a*Real.exp (-η);
         -b*Real.exp (-η), Real.exp (-η)] : M2R
    ) = 1 := by
  simp [Matrix.det_fin_two]
  have h : Real.exp η * Real.exp (-η) = 1 := by
    rw [← Real.exp_add]
    simp
  linarith

end GaussDecomposition
end SplitOctonionSL2MatrixBridge
