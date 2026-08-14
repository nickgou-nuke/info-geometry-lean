import Mathlib.Tactic
import InfoGeometry.Physics.YangBaxterQSwap

/-!
# Concrete non-symmetric Yang--Baxter matrix witness

This owner records a genuine finite-dimensional braid witness already present
in the repository.  It is deliberately not labelled a quantum `G₂` model:
the `G₂` provenance question remains separate.
-/

namespace InfoGeometry.Canonical.ConcreteNonSymmetricYBEMatrixWitness

open InfoGeometry.Physics.YangBaxterQSwap
open Matrix

def qWitness : ℂ := 2

def R12 : Matrix (Fin 8) (Fin 8) ℂ := C12 qWitness
def R23 : Matrix (Fin 8) (Fin 8) ℂ := C23 qWitness

theorem yangBaxter : R12 * R23 * R12 = R23 * R12 * R23 := by
  exact yang_baxter_relation qWitness

theorem R12_sq : R12 * R12 = (4 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R12, C12, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_eight, qWitness] <;> norm_num

theorem monodromy_ne_id : R12 * R12 ≠ (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  rw [R12_sq]
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num at h00

noncomputable def R12Inv : Matrix (Fin 8) (Fin 8) ℂ := (1 / 4 : ℂ) • R12

theorem R12_left_inverse : R12Inv * R12 = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  calc
    R12Inv * R12 = (1 / 4 : ℂ) • (R12 * R12) := by
      rw [R12Inv, Matrix.smul_mul]
    _ = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
      rw [R12_sq]
      norm_num

theorem R12_right_inverse : R12 * R12Inv = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  calc
    R12 * R12Inv = (1 / 4 : ℂ) • (R12 * R12) := by
      rw [R12Inv, Matrix.mul_smul]
    _ = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
      rw [R12_sq]
      norm_num

theorem R12_invertible : Function.Bijective (R12 * ·) := by
  constructor
  · intro X Y h
    have h' := congrArg (fun Z => R12Inv * Z) h
    rw [← Matrix.mul_assoc, R12_left_inverse] at h'
    simpa using h'
  · intro Y
    refine ⟨R12Inv * Y, ?_⟩
    change R12 * (R12Inv * Y) = Y
    rw [Matrix.mul_assoc, R12_right_inverse]
    simp

end InfoGeometry.Canonical.ConcreteNonSymmetricYBEMatrixWitness
