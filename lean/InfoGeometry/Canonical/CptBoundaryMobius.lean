import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.CptBoundaryMobius

open Matrix

/-! A finite integer matrix involution and its action on two projectors. -/

/-- Predicate for a square involution in the finite matrix carrier. -/
def CptInvolution (CPT : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  CPT * CPT = 1

namespace CptInvolution

theorem is_involution {CPT : Matrix (Fin 2) (Fin 2) ℤ}
    (h : CptInvolution CPT) : CPT * CPT = 1 := h

end CptInvolution

/-- The explicit integer matrix used by the finite boundary packet. -/
def CPT_local : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, -1;
     -1, 0]

/-- The first diagonal projector. -/
def P_zero : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0;
     0, 0]

/-- The complementary diagonal projector. -/
def L_spectator : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 0;
     0, 1]

/-- The explicit matrix is a square involution. -/
theorem CPT_local_is_involution :
    CptInvolution CPT_local := by
  unfold CptInvolution
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CPT_local, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Conjugation by the involution exchanges the two diagonal projectors. -/
theorem moebius_zero_infinity_duality :
    CPT_local * P_zero * CPT_local = L_spectator := by
  dsimp [CPT_local, P_zero, L_spectator]
  decide

end InfoGeometry.Canonical.CptBoundaryMobius
