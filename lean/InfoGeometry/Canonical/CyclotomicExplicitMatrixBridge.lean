import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Concrete, representation-neutral matrix witnesses for the low cyclotomic
 stages.  These witnesses are kept separate from the operator-valued spine:
 they do not assert a `G₂` or Clifford interpretation. -/

namespace InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge

abbrev M3 := Matrix (Fin 3) (Fin 3) ℤ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℤ
abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ
abbrev M8 := Matrix (Fin 8) (Fin 8) ℤ

def tripotent : M3 := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem tripotent_cube : tripotent ^ 3 = tripotent := by
  native_decide

def complexStage : M3 := !![0, -1, 0; 1, 0, 0; 0, 0, 0]

theorem complexStage_cube : complexStage ^ 3 = -complexStage := by
  native_decide

def phi6Companion : M2 := !![0, -1; 1, 1]

theorem phi6Companion_order : phi6Companion ^ 6 = 1 := by
  native_decide

def phi8Companion : M4 :=
  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

theorem phi8Companion_fourth : phi8Companion ^ 4 = -1 := by
  native_decide

theorem phi8Companion_order : phi8Companion ^ 8 = 1 := by
  calc
    phi8Companion ^ 8 = (phi8Companion ^ 4) ^ 2 := by
      rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
    _ = 1 := by rw [phi8Companion_fourth]; native_decide

def phi12Companion : M4 :=
  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0]

theorem phi12Companion_order : phi12Companion ^ 12 = 1 := by
  native_decide

def phi24Companion : M8 :=
  !![0, 0, 0, 0, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0]

theorem phi24Companion_order : phi24Companion ^ 24 = 1 := by
  native_decide

end InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge
