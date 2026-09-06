import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.KleinExceptionalBraid

open Matrix

/-!
# Finite matrix identities for a glide and a quarter-turn

This owner contains only the displayed integer `2 × 2` matrices and their
kernel-checked products.  It does not formalize a Brillouin zone, exceptional
point topology, or a physical Berry-phase transport.
-/

/-- A concrete integer `2 × 2` quarter-turn matrix. -/
def B_EP : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![0, -1],
    ![1,  0]]

/-- A concrete integer `2 × 2` basis-swap matrix. -/
def G_Glide : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![0, 1],
    ![1, 0]]

/-- The basis-swap matrix squares to the identity. -/
theorem glide_involution :
    G_Glide * G_Glide = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G_Glide, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugation by the basis-swap matrix negates the quarter-turn matrix. -/
theorem klein_twist_anti_isomorphism :
    G_Glide * B_EP * G_Glide = - B_EP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G_Glide, B_EP, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.KleinExceptionalBraid
