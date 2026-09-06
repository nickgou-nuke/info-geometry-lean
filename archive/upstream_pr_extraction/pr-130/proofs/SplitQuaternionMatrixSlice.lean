import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
namespace SplitQuaternionMatrixSlice

/-- Coordinate carrier for the 4D associative slice span{1, u, ℓ, uℓ} -/
@[ext]
structure SQCoord where
  c1 : ℝ
  cu : ℝ
  cell : ℝ
  cuell : ℝ

/-- The exact coordinate product derived from Split-Octonion multiplication -/
def coordMul (x y : SQCoord) : SQCoord :=
  ⟨
    x.c1 * y.c1 - x.cu * y.cu + x.cell * y.cell + x.cuell * y.cuell,
    x.c1 * y.cu + x.cu * y.c1 - x.cell * y.cuell + x.cuell * y.cell,
    x.c1 * y.cell - x.cu * y.cuell + x.cell * y.c1 + x.cuell * y.cu,
    x.c1 * y.cuell + x.cu * y.cell - x.cell * y.cu + x.cuell * y.c1
  ⟩

/-- Matrix representation Phi mapping to M_2(ℝ) -/
def Phi (x : SQCoord) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x.c1 + x.cell, -x.cu + x.cuell;
     x.cu + x.cuell, x.c1 - x.cell]

/-- The decisive theorem: Phi is a multiplicative homomorphism -/
theorem Phi_mul_eq_matrix_mul (x y : SQCoord) :
    Phi (coordMul x y) = Phi x * Phi y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phi, coordMul, Matrix.mul_apply] <;> ring

theorem Phi_injective : Function.Injective Phi := by
  intro x y h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  simp [Phi] at h00 h01 h10 h11
  ext <;> linarith

theorem Phi_surjective : Function.Surjective Phi := by
  intro M
  let x : SQCoord :=
    ⟨(M 0 0 + M 1 1) / 2,
      (M 1 0 - M 0 1) / 2,
      (M 0 0 - M 1 1) / 2,
      (M 1 0 + M 0 1) / 2⟩
  refine ⟨x, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x, Phi] <;> ring

/-- Exact unipotent matrix exponentials for aE and bF in the selected basis -/
theorem Phi_exp_aE (a : ℝ) :
    Phi ⟨1, a / 2, 0, -a / 2⟩ = !![1, -a; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phi] <;> ring

theorem Phi_exp_bF (b : ℝ) :
    Phi ⟨1, -b / 2, 0, -b / 2⟩ = !![1, 0; -b, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phi]

/-- Full exact open Gauss cell decomposition -/
theorem gauss_cell_decomposition (a η b : ℝ) :
    !![1, -a; 0, 1] * !![Real.exp η, 0; 0, Real.exp (-η)] * !![1, 0; -b, 1] =
    !![Real.exp η + a * b * Real.exp (-η), -a * Real.exp (-η);
       -b * Real.exp (-η), Real.exp (-η)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply] <;> ring

theorem gauss_cell_det_one (a η b : ℝ) :
    Matrix.det !![Real.exp η + a * b * Real.exp (-η), -a * Real.exp (-η);
                  -b * Real.exp (-η), Real.exp (-η)] = 1 := by
  simp [Matrix.det_fin_two]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero η]
  ring

end SplitQuaternionMatrixSlice
end noncomputable section
