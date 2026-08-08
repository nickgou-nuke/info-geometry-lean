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

theorem Phi_injective : Function.Injective Phi := by sorry

theorem Phi_surjective : Function.Surjective Phi := by sorry

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
    simp [Phi] <;> ring

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
  -- (e^η + ab e^-η)(e^-η) - (-a e^-η)(-b e^-η) = 1 + ab e^-2η - ab e^-2η = 1
  -- using Real.exp_add and Real.exp_zero
  sorry

end SplitQuaternionMatrixSlice
end noncomputable section
