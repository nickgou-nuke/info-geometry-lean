import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Physics.SplitOctonionBraidSU3

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace ZornOctonionAnyon

open InfoGeometry.Physics.SplitOctonionBraidSU3

/-- Zorn Split Octonion Matrix Cell Z = (a, b, v, w) with scalars a, b ∈ ℂ and color 3-vectors v, w ∈ ℂ³. -/
abbrev ZornCell :=
  InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn

namespace ZornCell

/-- Dot product pairing for color vectors v • w = ∑ v_i w_i. -/
abbrev colorDot :=
  InfoGeometry.Physics.SplitOctonionBraidSU3.dot3

/-- Zorn Split Octonion Norm/Determinant: det(Z) = a * b - v • w. -/
abbrev detZ :=
  InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm

def offDiagonal (v w : Fin 3 → ℂ) : ZornCell where
  a := 0
  u := v
  v := w
  b := 0

/-- **Theorem**: Pure Off-Diagonal Null Cone Boundary Condition (a = 0, b = 0):
    det(Z) = - (v • w). -/
theorem det_off_diagonal_null_cone (v w : Fin 3 → ℂ) :
    detZ (offDiagonal v w) = - colorDot v w := by
  simp [detZ, offDiagonal, colorDot,
    InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm,
    InfoGeometry.Physics.SplitOctonionBraidSU3.dot3]

/-- Color Pair Tensor Product Matrix M_{ij} = v_i * w_j in M₃(ℂ). -/
def colorTensorMatrix (v w : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => v i * w j

/-- **Theorem**: Cayley-Dickson Hypercomplex Pairing Trace Identity:
    Tr(v ⊗ w) = v • w. -/
theorem color_tensor_trace_eq_dot (v w : Fin 3 → ℂ) :
    trace (colorTensorMatrix v w) = colorDot v w := by
  dsimp [colorTensorMatrix, trace]
  rw [Fin.sum_univ_three]
  rfl

/-- **Theorem**: Null Boundary Anyon Braiding Pairing Vanishing:
    If v • w = 0 on the Zorn null boundary, then Tr(v ⊗ w) = 0. -/
theorem null_boundary_color_pairing_zero (v w : Fin 3 → ℂ) (h_null : colorDot v w = 0) :
    trace (colorTensorMatrix v w) = 0 := by
  rw [color_tensor_trace_eq_dot, h_null]

/-- **Theorem**: Gell-Mann SU(3) Unitary Color Gauge Action Trace Invariance:
    Tr(U * (v ⊗ w) * U⁻¹) = Tr(v ⊗ w). -/
theorem gellmann_su3_gauge_trace_invariant (U U_inv : Matrix (Fin 3) (Fin 3) ℂ) (v w : Fin 3 → ℂ) (h_inv : U_inv * U = 1) :
    trace (U * colorTensorMatrix v w * U_inv) = trace (colorTensorMatrix v w) := by
  have h_comm : trace (U * colorTensorMatrix v w * U_inv) = trace (U_inv * (U * colorTensorMatrix v w)) := trace_mul_comm (U * colorTensorMatrix v w) U_inv
  rw [h_comm]
  have h_assoc : U_inv * (U * colorTensorMatrix v w) = (U_inv * U) * colorTensorMatrix v w := by
    rw [← Matrix.mul_assoc]
  rw [h_assoc, h_inv, one_mul]

end ZornCell

end ZornOctonionAnyon
