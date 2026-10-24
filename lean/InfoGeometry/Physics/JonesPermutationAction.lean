/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.B3PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! A native permutation representation on the Jones eight-state carrier.
Generator identification with the TL matrices is a separate checked bridge. -/

noncomputable section
namespace InfoGeometry.Physics.JonesPermutationAction

open B3PresentedGroup

abbrev States := Fin 2 ⊕ (Fin 2 × Fin 3)

def encode : States → Fin 8
  | .inl i => ![0, 7] i
  | .inr (b, i) => (![![4, 2, 1], ![3, 5, 6]] : Fin 2 → Fin 3 → Fin 8) b i

def decode : Fin 8 → States :=
  ![.inl 0, .inr (0, 2), .inr (0, 1), .inr (1, 0),
    .inr (0, 0), .inr (1, 1), .inr (1, 2), .inl 1]

def stateEquiv : States ≃ Fin 8 where
  toFun := encode
  invFun := decode
  left_inv := by decide
  right_inv := by decide

def blockAction : Equiv.Perm (Fin 3) →* Equiv.Perm States where
  toFun σ := Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) σ)
  map_one' := by ext x; cases x <;> rfl
  map_mul' σ τ := by ext x; cases x <;> rfl

def stateAction : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 8) where
  toFun σ := stateEquiv.permCongr (blockAction σ)
  map_one' := by ext x; simp [Equiv.permCongr_apply]
  map_mul' σ τ := by
    ext x
    simp [Equiv.permCongr_apply, map_mul]

def signMatrix : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal ![1, 1, -1, 1, 1, -1, 1, 1]

/-- Upper off-diagonal matrix unit in `M₈(ℂ)`. -/
def mat8Unit01C : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- Lower off-diagonal matrix unit in `M₈(ℂ)`. -/
def mat8Unit10C : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Noncommutativity witness for `M₈(ℂ)`. -/
theorem mat8_units_noncommute_complex :
    mat8Unit01C * mat8Unit10C ≠ mat8Unit10C * mat8Unit01C := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℂ => M 0 0) h
  have h10 : (1 : ℂ) = 0 := by
    simpa [mat8Unit01C, mat8Unit10C, Matrix.mul_apply, Fin.sum_univ_eight] using h00
  exact one_ne_zero h10

theorem signMatrix_sq : signMatrix * signMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [signMatrix, Matrix.mul_apply, Fin.sum_univ_eight]

def permutationMatrix : Equiv.Perm (Fin 3) →* Matrix (Fin 8) (Fin 8) ℂ :=
  (Matrix.permMatrixHom (R := ℂ)).comp stateAction

def signedMatrix : Equiv.Perm (Fin 3) →* Matrix (Fin 8) (Fin 8) ℂ where
  toFun σ := signMatrix * permutationMatrix σ * signMatrix
  map_one' := by simp [signMatrix_sq]
  map_mul' σ τ := by
    rw [map_mul]
    calc signMatrix * (permutationMatrix σ * permutationMatrix τ) * signMatrix =
        signMatrix * permutationMatrix σ * (signMatrix * signMatrix) *
          permutationMatrix τ * signMatrix := by rw [signMatrix_sq]; simp [mul_assoc]
      _ = _ := by simp only [mul_assoc]

def rho : Equiv.Perm (Fin 3) →* GL8 := signedMatrix.toHomUnits

end InfoGeometry.Physics.JonesPermutationAction
