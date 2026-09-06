import Mathlib.Tactic
import InfoGeometry.Physics.YangBaxterQSwap

/-!
# Concrete non-symmetric Yang--Baxter matrix

This owner records a genuine finite-dimensional braid relation and its
associated invertible monodromy matrix.
-/

namespace InfoGeometry.Canonical.ConcreteNonSymmetricYBEMatrix

open InfoGeometry.Physics.YangBaxterQSwap
open Matrix

def R12 : Matrix (Fin 8) (Fin 8) ℂ := C12 2
def R23 : Matrix (Fin 8) (Fin 8) ℂ := C23 2

theorem yangBaxter : R12 * R23 * R12 = R23 * R12 * R23 := by
  exact yang_baxter_relation 2

theorem R12_sq : R12 * R12 = (4 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R12, C12, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_eight] <;> norm_num

theorem monodromy_ne_id : R12 * R12 ≠ (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  rw [R12_sq]
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num at h00

noncomputable def R12Inv : Matrix (Fin 8) (Fin 8) ℂ := (1 / 4 : ℂ) • R12

theorem R12_left_inverse : R12Inv * R12 = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  dsimp [R12Inv]
  rw [Matrix.smul_mul, R12_sq, smul_smul]
  have : (1 / 4 : ℂ) * 4 = 1 := by norm_num
  rw [this, one_smul]

theorem R12_right_inverse : R12 * R12Inv = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  dsimp [R12Inv]
  rw [Matrix.mul_smul, R12_sq, smul_smul]
  have : (1 / 4 : ℂ) * 4 = 1 := by norm_num
  rw [this, one_smul]

theorem R12_invertible : Function.Bijective (fun X => R12 * X) := by
  constructor
  · intro X Y (h : R12 * X = R12 * Y)
    have h' : R12Inv * (R12 * X) = R12Inv * (R12 * Y) := by rw [h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, R12_left_inverse, Matrix.one_mul,
      Matrix.one_mul] at h'
    exact h'
  · intro Y
    refine ⟨R12Inv * Y, ?_⟩
    dsimp
    rw [← Matrix.mul_assoc, R12_right_inverse, Matrix.one_mul]

end InfoGeometry.Canonical.ConcreteNonSymmetricYBEMatrix
