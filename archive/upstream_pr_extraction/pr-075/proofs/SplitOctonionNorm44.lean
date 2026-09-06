import proofs.SplitOctonionAlgebra
import proofs.SplitOctonionQuaternionChart
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic

open SplitOctonion
open Quaternion

namespace SplitOctonionNorm44

/-- The split norm is defined as the Cayley-Dickson norm of (x, y), which is Q(x) - Q(y).
    Here Q is the standard positive definite quaternion norm. -/
noncomputable def splitNorm (z : SplitOct) : ℝ :=
  (z.a.re * z.a.re + z.a.imI * z.a.imI + z.a.imJ * z.a.imJ + z.a.imK * z.a.imK) -
  (z.b.re * z.b.re + z.b.imI * z.b.imI + z.b.imJ * z.b.imJ + z.b.imK * z.b.imK)

/-- The polarization identity defines the symmetric bilinear form. -/
noncomputable def splitBilinear (x y : SplitOct) : ℝ :=
  (splitNorm (x + y) - splitNorm x - splitNorm y) / 2

theorem splitBilinear_symmetric (x y : SplitOct) :
  splitBilinear x y = splitBilinear y x := by
  dsimp [splitBilinear, splitNorm, add_def]
  ring

/-- The canonical basis of Split Octonions -/
def basis (i : Fin 8) : SplitOct :=
  match i with
  | 0 => ⟨1, 0⟩
  | 1 => ⟨⟨0, 1, 0, 0⟩, 0⟩
  | 2 => ⟨⟨0, 0, 1, 0⟩, 0⟩
  | 3 => ⟨⟨0, 0, 0, 1⟩, 0⟩
  | 4 => ⟨0, 1⟩
  | 5 => ⟨0, ⟨0, 1, 0, 0⟩⟩
  | 6 => ⟨0, ⟨0, 0, 1, 0⟩⟩
  | 7 => ⟨0, ⟨0, 0, 0, 1⟩⟩

/-- The Gram matrix of the split bilinear form in the canonical basis. -/
noncomputable def splitGram : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of (fun i j => splitBilinear (basis i) (basis j))

/-- The diagonal matrix of signature (4, 4) -/
noncomputable def diag4444 : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.diagonal (fun i => if i.val < 4 then 1 else -1)

theorem splitGram_eq_diag_4444 : splitGram = diag4444 := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
  simp [splitGram, diag4444, splitBilinear, splitNorm, basis, add_def] <;> norm_num

theorem splitBilinear_nondegenerate (x : SplitOct) (h : ∀ y : SplitOct, splitBilinear x y = 0) : x = 0 := by
  have h0 := h (basis 0); dsimp [splitBilinear, splitNorm, basis, add_def] at h0; have r0 : x.a.re = 0 := by linarith
  have h1 := h (basis 1); dsimp [splitBilinear, splitNorm, basis, add_def] at h1; have r1 : x.a.imI = 0 := by linarith
  have h2 := h (basis 2); dsimp [splitBilinear, splitNorm, basis, add_def] at h2; have r2 : x.a.imJ = 0 := by linarith
  have h3 := h (basis 3); dsimp [splitBilinear, splitNorm, basis, add_def] at h3; have r3 : x.a.imK = 0 := by linarith
  have h4 := h (basis 4); dsimp [splitBilinear, splitNorm, basis, add_def] at h4; have r4 : x.b.re = 0 := by linarith
  have h5 := h (basis 5); dsimp [splitBilinear, splitNorm, basis, add_def] at h5; have r5 : x.b.imI = 0 := by linarith
  have h6 := h (basis 6); dsimp [splitBilinear, splitNorm, basis, add_def] at h6; have r6 : x.b.imJ = 0 := by linarith
  have h7 := h (basis 7); dsimp [splitBilinear, splitNorm, basis, add_def] at h7; have r7 : x.b.imK = 0 := by linarith
  ext1 <;> ext1
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7

/--
The Lie algebra so(4,4) is the space of endomorphisms skew-adjoint with respect to the split norm.
We define so44 as a subtype of ℝ-linear maps.
-/
structure so44 where
  toLinearMap : SplitOct →ₗ[ℝ] SplitOct
  skew' : ∀ x y, splitBilinear (toLinearMap x) y + splitBilinear x (toLinearMap y) = 0

end SplitOctonionNorm44
