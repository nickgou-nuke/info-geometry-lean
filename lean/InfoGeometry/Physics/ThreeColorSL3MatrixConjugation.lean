import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Matrix
import InfoGeometry.Physics.GellMannSU3

/-!
# Continuous `SL₃` conjugation on the three-color `3×3` matrix carrier

This owner keeps the external `SL₃` layer separate from the Zorn carrier.
It packages the standard conjugation action on `M₃(ℂ)` and records the
continuity and commutator transport laws needed by the Gell-Mann layer.

No claim is made that this is an `SU(3)` representation; it is the algebraic
`SL₃` transport bridge.
-/

namespace InfoGeometry.Physics.ThreeColorSL3MatrixConjugation

noncomputable section

open Matrix
open InfoGeometry.Physics.GellMannSU3

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev SL3C := Matrix.SpecialLinearGroup (Fin 3) ℂ

/-- Conjugation by an `SL₃` matrix on the `3×3` carrier. -/
noncomputable def sl3ConjAct (g : SL3C) (A : M3C) : M3C :=
  (g : M3C) * A * (g⁻¹ : M3C)

@[simp] theorem sl3ConjAct_one (A : M3C) :
    sl3ConjAct (1 : SL3C) A = A := by
  simp [sl3ConjAct]

theorem sl3ConjAct_mul (g h : SL3C) (A : M3C) :
    sl3ConjAct (g * h) A = sl3ConjAct g (sl3ConjAct h A) := by
  simp [sl3ConjAct, mul_assoc, Matrix.mul_inv_rev]

theorem sl3ConjAct_add (g : SL3C) (A B : M3C) :
    sl3ConjAct g (A + B) = sl3ConjAct g A + sl3ConjAct g B := by
  simp [sl3ConjAct, mul_add, add_mul, mul_assoc]

theorem sl3ConjAct_mul_matrix (g : SL3C) (A B : M3C) :
    sl3ConjAct g (A * B) = sl3ConjAct g A * sl3ConjAct g B := by
  simp [sl3ConjAct, mul_assoc]

theorem sl3ConjAct_commutator (g : SL3C) (A B : M3C) :
    sl3ConjAct g (A * B - B * A) =
      sl3ConjAct g A * sl3ConjAct g B -
        sl3ConjAct g B * sl3ConjAct g A := by
  calc
    sl3ConjAct g (A * B - B * A)
        = sl3ConjAct g (A * B) - sl3ConjAct g (B * A) := by
            simp [sl3ConjAct, mul_add, add_mul, sub_eq_add_neg, mul_assoc]
    _ = sl3ConjAct g A * sl3ConjAct g B -
        sl3ConjAct g B * sl3ConjAct g A := by
            rw [sl3ConjAct_mul_matrix, sl3ConjAct_mul_matrix]

/-- A general commutator transport theorem under `SL₃` conjugation. -/
theorem sl3ConjAct_transport
    (g : SL3C) (A B C : M3C) (c : ℂ)
    (h : A * B - B * A = c • C) :
    sl3ConjAct g A * sl3ConjAct g B -
        sl3ConjAct g B * sl3ConjAct g A =
      c • sl3ConjAct g C := by
  calc
    sl3ConjAct g A * sl3ConjAct g B -
        sl3ConjAct g B * sl3ConjAct g A
        = sl3ConjAct g (A * B - B * A) := by
            symm
            exact sl3ConjAct_commutator g A B
    _ = sl3ConjAct g (c • C) := by rw [h]
    _ = c • sl3ConjAct g C := by simp [sl3ConjAct]

end

end InfoGeometry.Physics.ThreeColorSL3MatrixConjugation
