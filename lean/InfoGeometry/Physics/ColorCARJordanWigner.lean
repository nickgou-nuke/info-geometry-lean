/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ColorCARStandardModel

/-!
# Jordan–Wigner three-mode CAR on the Furey tensor carrier

The local operators `carAnn i`, `carCre i` of `ColorCARStandardModel` act on
separate tensor factors with no parity string; distinct modes commute, so the
cross-mode anticommutator is nonzero (`carAnn0_carAnn1_anticomm_ne_zero`).

This file inserts the Jordan–Wigner parity strings `σ₃ ⊗ …` and proves the full
three-mode canonical anticommutation relations on the same carrier `CAR3`:

* `jwAnn_anticomm`     : `{aᵢ, aⱼ} = 0`
* `jwCre_anticomm`     : `{aᵢ†, aⱼ†} = 0`
* `jwAnn_jwCre_anticomm` : `{aᵢ, aⱼ†} = δᵢⱼ · 1`

It also records how the signed operators relate to the local ones: mode `0` is
unchanged, and the number operators coincide (`jw_number_eq`), so the existing
number-projector and vacuum-ideal results apply verbatim.

No physical particle identification is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.ColorCARJordanWigner

open TensorProduct
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Physics.ColorCARStandardModel

/-! ## Refutation: the local operators are not cross-mode fermionic -/

/-- A linear readout `(a ⊗ b) ⊗ c ↦ a₀₁ · b₀₁ · c₀₀` detecting `σ⁺ ⊗ σ⁺ ⊗ 1`
(`CAR3` is left-associated: `(M2C ⊗ M2C) ⊗ M2C`). -/
def readout01 : CAR3 →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun (x : M2C ⊗[ℂ] M2C) (c : M2C) =>
        TensorProduct.lift
          (LinearMap.mk₂ ℂ (fun (a b : M2C) => a 0 1 * b 0 1)
            (fun a₁ a₂ b => by simp [add_mul])
            (fun r a b => by simp [mul_assoc])
            (fun a b₁ b₂ => by simp [mul_add])
            (fun r a b => by simp; ring)) x * c 0 0)
      (fun x₁ x₂ c => by simp [add_mul])
      (fun r x c => by simp [mul_assoc])
      (fun x c₁ c₂ => by simp [mul_add])
      (fun r x c => by simp; ring))

theorem readout01_tmul (a b c : M2C) :
    readout01 (a ⊗ₜ[ℂ] b ⊗ₜ[ℂ] c) = a 0 1 * b 0 1 * c 0 0 := by
  simp [readout01]

/-- The local operators on modes `0` and `1` fail cross-mode anticommutation. -/
theorem carAnn0_carAnn1_anticomm_ne_zero :
    carAnn0 * carAnn1 + carAnn1 * carAnn0 ≠ 0 := by
  intro h
  have h2 := congrArg readout01 h
  simp [carAnn0, carAnn1, Algebra.TensorProduct.tmul_mul_tmul, readout01_tmul,
    σPlus] at h2

/-! ## Jordan–Wigner signed operators -/

/-- Jordan–Wigner annihilators `a₀ = σ⁺⊗1⊗1`, `a₁ = σ₃⊗σ⁺⊗1`, `a₂ = σ₃⊗σ₃⊗σ⁺`. -/
def jwAnn : Fin 3 → CAR3
  | 0 => σPlus ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] (1 : M2C)
  | 1 => σ3c ⊗ₜ[ℂ] σPlus ⊗ₜ[ℂ] (1 : M2C)
  | 2 => σ3c ⊗ₜ[ℂ] σ3c ⊗ₜ[ℂ] σPlus

/-- Jordan–Wigner creators `a₀† = σ⁻⊗1⊗1`, `a₁† = σ₃⊗σ⁻⊗1`, `a₂† = σ₃⊗σ₃⊗σ⁻`. -/
def jwCre : Fin 3 → CAR3
  | 0 => σMinus ⊗ₜ[ℂ] (1 : M2C) ⊗ₜ[ℂ] (1 : M2C)
  | 1 => σ3c ⊗ₜ[ℂ] σMinus ⊗ₜ[ℂ] (1 : M2C)
  | 2 => σ3c ⊗ₜ[ℂ] σ3c ⊗ₜ[ℂ] σMinus

theorem jwAnn_zero : jwAnn 0 = carAnn0 := rfl
theorem jwCre_zero : jwCre 0 = carCre0 := rfl

/-! ## Three-mode CAR -/

theorem jwAnn_anticomm (i j : Fin 3) :
    jwAnn i * jwAnn j + jwAnn j * jwAnn i = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [jwAnn, Algebra.TensorProduct.tmul_mul_tmul, σPlus_sq, σ3c_sq,
      σ3c_mul_σPlus, σPlus_mul_σ3c, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

theorem jwCre_anticomm (i j : Fin 3) :
    jwCre i * jwCre j + jwCre j * jwCre i = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [jwCre, Algebra.TensorProduct.tmul_mul_tmul, σMinus_sq, σ3c_sq,
      σ3c_mul_σMinus, σMinus_mul_σ3c, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

theorem jwAnn_jwCre_anticomm (i j : Fin 3) :
    jwAnn i * jwCre j + jwCre j * jwAnn i = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [jwAnn, jwCre, Algebra.TensorProduct.tmul_mul_tmul, σ3c_sq,
      σ3c_mul_σPlus, σPlus_mul_σ3c, σ3c_mul_σMinus, σMinus_mul_σ3c,
      TensorProduct.neg_tmul, TensorProduct.tmul_neg, ← TensorProduct.add_tmul,
      ← TensorProduct.tmul_add, anti_σPlus_σMinus, Algebra.TensorProduct.one_def]

/-- Annihilators are nilpotent of order two. -/
theorem jwAnn_sq (i : Fin 3) : jwAnn i * jwAnn i = 0 := by
  fin_cases i <;> simp [jwAnn, Algebra.TensorProduct.tmul_mul_tmul, σPlus_sq]

/-- Creators are nilpotent of order two. -/
theorem jwCre_sq (i : Fin 3) : jwCre i * jwCre i = 0 := by
  fin_cases i <;> simp [jwCre, Algebra.TensorProduct.tmul_mul_tmul, σMinus_sq]

/-! ## Relation to the existing local number operators -/

/-- The parity strings cancel in `aᵢ aᵢ†`: the Jordan–Wigner number operators
coincide with the existing `numberOp0/1/2`. -/
theorem jw_number_eq_numberOp0 : jwAnn 0 * jwCre 0 = numberOp0 := rfl

theorem jw_number_eq_numberOp1 : jwAnn 1 * jwCre 1 = numberOp1 := by
  simp [jwAnn, jwCre, numberOp1, carAnn1, carCre1,
    Algebra.TensorProduct.tmul_mul_tmul, σ3c_sq]

theorem jw_number_eq_numberOp2 : jwAnn 2 * jwCre 2 = numberOp2 := by
  simp [jwAnn, jwCre, numberOp2, carAnn2, carCre2,
    Algebra.TensorProduct.tmul_mul_tmul, σ3c_sq]

end InfoGeometry.Physics.ColorCARJordanWigner
