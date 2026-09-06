import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Liu-Collins Affine Invariance Theorem

Formalizes Section 4.2 of Liu & Collins (1998): "Frieze and Wallpaper 
Symmetry Groups Classification under Affine and Perspective Distortion".

Proves the universal topological robustness of the `C₂` (2-fold rotation/inversion) 
symmetry under any arbitrary affine transformation, establishing the geometric 
resilience of the parity/grading operator `Γ` in our holographic superalgebra.
-/

namespace LiuCollins

open Matrix

/-- The `C₂` (180° rotation / spatial inversion) matrix in 2D. -/
def C2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, 0; 0, -1]

/-- 
Theorem (Liu-Collins 4.2.1): 
The `C₂` matrix commutes exactly with ANY arbitrary affine transformation matrix `A`.

`A * C₂ = C₂ * A`

This mathematically guarantees that if a boundary pattern `S` has `C₂` symmetry 
(i.e. `g(S) = S`), the affinely distorted pattern `A(S)` preserves it unconditionally
because `g(A(S)) = A(g(S)) = A(S)`. 
-/
theorem C2_commutes_all_affine (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A * C2 = C2 * A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C2, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- A pure reflection across the x-axis. -/
def Rx : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- A non-uniform parallel/perpendicular scaling matrix. -/
def Scale (sx sy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![sx, 0; 0, sy]

/-- 
Theorem (Liu-Collins 4.2.2):
Reflections survive non-uniform parallel/perpendicular scalings because 
the scaling matrix structurally commutes with the reflection.
-/
theorem Rx_commutes_scaling (sx sy : ℝ) :
    Scale sx sy * Rx = Rx * Scale sx sy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx, Scale, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

end LiuCollins
