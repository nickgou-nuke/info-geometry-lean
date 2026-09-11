import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace PenroseCuntzKriegerHolography

open Matrix

abbrev Z2 := InfoGeometry.Algebra.FiniteSpin.Vec2Z
abbrev M2Z := InfoGeometry.Algebra.FiniteSpin.Mat2Z

def M : M2Z := !![2, 1; 1, 1]

def B : M2Z := !![-1, -1; -1, 0]

def C : M2Z := !![0, -1; -1, 1]

theorem B_eq_I_sub_MT : B = (1 : M2Z) - Mᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, M]

def traceM : ℤ := 2 + 1

theorem M_det : M.det = 1 := by norm_num [M, Matrix.det_fin_two]

theorem B_det : B.det = -1 := by norm_num [B, Matrix.det_fin_two]

theorem B_mul_C : B * C = (1 : M2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, C, Matrix.mul_apply]

theorem C_mul_B : C * B = (1 : M2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, C, Matrix.mul_apply]

def ckMap (v : Z2) : Z2 := B.mulVec v

theorem ckMap_surjective : Function.Surjective ckMap := by
  intro v
  use C.mulVec v
  ext i
  fin_cases i <;>
    simp [ckMap, B, C, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem ckMap_eq_zero (v : Z2) (h : ckMap v = 0) : v = 0 := by
  have hleft : C.mulVec (ckMap v) = v := by
    ext i
    fin_cases i <;>
      simp [ckMap, B, C, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [← hleft, h]
  ext i
  fin_cases i <;>
    simp [C, Matrix.mulVec, dotProduct]

def cantorCylinderCount (n : ℕ) : ℕ := 2 ^ n

theorem cantorCylinder_refines (n : ℕ) :
    cantorCylinderCount (n + 1) = 2 * cantorCylinderCount n := by
  simp [cantorCylinderCount, pow_succ]
  ring

def PenroseCantorSpace : Type := ℕ → Bool

theorem penroseCantorSpace_equiv : Nonempty (PenroseCantorSpace ≃ (ℕ → Bool)) := by
  exact ⟨Equiv.refl _⟩

end PenroseCuntzKriegerHolography
