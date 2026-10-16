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

* `jwAnn_anticomm`       : `{aᵢ, aⱼ} = 0`
* `jwCre_anticomm`       : `{aᵢ†, aⱼ†} = 0`
* `jwAnn_jwCre_anticomm` : `{aᵢ, aⱼ†} = δᵢⱼ · 1`

It also records how the signed operators relate to the local factor projectors
and vacuum idempotent at each of the three fixed modes:

* `jw_number_eq_numberOp0/1/2`         : `jwAnn i * jwCre i = numberOp{0,1,2}`
  ($a_i a_i^\dagger = N_+$ on factor $i$, the vacancy projector for $a_i = \sigma^+$)
* `jw_excitation_eq_excitationOp0/1/2` : `jwCre i * jwAnn i = excitationOp{0,1,2}`
  ($a_i^\dagger a_i = N_-$ on factor $i$, the particle excitation projector for
  $a_i^\dagger = \sigma^-$)
* `jwAnn_mul_fureyVacuumIdempotent`    : `jwAnn i * fureyVacuumIdempotent = 0`

No physical particle identification is asserted.

The repository also has a real-valued arbitrary-stage Jordan--Wigner tower in
`InfoGeometry.Clifford.Cl11TensorTower`. This module is the separate complex
three-factor realization used by the Furey tensor carrier. No theorem here
identifies those two carriers or their operator families; such an identification
requires an explicit algebra equivalence and compatibility proof.
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
            (fun r a b => by simp only [Matrix.smul_apply, smul_eq_mul]; exact mul_left_comm _ _ _)) x * c 0 0)
      (fun x₁ x₂ c => by simp [add_mul])
      (fun r x c => by simp [mul_assoc])
      (fun x c₁ c₂ => by simp [mul_add])
      (fun r x c => by simp only [Matrix.smul_apply, smul_eq_mul]; exact mul_left_comm _ _ _))

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

/-! ## Relation to the local factor projectors and vacuum idempotent

Because `σ₃² = 1`, the Jordan–Wigner parity strings cancel in both quadratic
combinations on a single mode:
* `jwAnn i * jwCre i = numberOp{0,1,2}` ($a_i a_i^\dagger = N_+$ on factor $i$,
  the vacancy projector for $a_i = \sigma^+$)
* `jwCre i * jwAnn i = excitationOp{0,1,2}` ($a_i^\dagger a_i = N_-$ on factor $i$,
  the particle excitation projector for $a_i^\dagger = \sigma^-$)

Furthermore, because `σ₃ N₊ = N₊` and `σ⁺ N₊ = 0`, every Jordan–Wigner
annihilator `jwAnn i` annihilates `fureyVacuumIdempotent = N₊ ⊗ N₊ ⊗ N₊`. -/

/-- The parity strings cancel in `aᵢ aᵢ†`: `jwAnn i * jwCre i` coincides with
the positive-chiral vacancy projector `numberOp0/1/2`. -/
theorem jw_number_eq_numberOp0 : jwAnn 0 * jwCre 0 = numberOp0 := rfl

theorem jw_number_eq_numberOp1 : jwAnn 1 * jwCre 1 = numberOp1 := by
  simp [jwAnn, jwCre, numberOp1, carAnn1, carCre1,
    Algebra.TensorProduct.tmul_mul_tmul, σ3c_sq]

theorem jw_number_eq_numberOp2 : jwAnn 2 * jwCre 2 = numberOp2 := by
  simp [jwAnn, jwCre, numberOp2, carAnn2, carCre2,
    Algebra.TensorProduct.tmul_mul_tmul, σ3c_sq]

/-- The parity strings cancel in `aᵢ† aᵢ`: `jwCre i * jwAnn i` coincides with
the negative-chiral particle excitation projector `excitationOp0/1/2`. -/
theorem jw_excitation_eq_excitationOp0 : jwCre 0 * jwAnn 0 = excitationOp0 := rfl

theorem jw_excitation_eq_excitationOp1 : jwCre 1 * jwAnn 1 = excitationOp1 := by
  simp [jwCre, jwAnn, excitationOp1, carCre1, carAnn1,
    Algebra.TensorProduct.tmul_mul_tmul, σ3c_sq]

theorem jw_excitation_eq_excitationOp2 : jwCre 2 * jwAnn 2 = excitationOp2 := by
  simp [jwCre, jwAnn, excitationOp2, carCre2, carAnn2,
    Algebra.TensorProduct.tmul_mul_tmul, σ3c_sq]

/-- Every Jordan–Wigner annihilator annihilates `fureyVacuumIdempotent`. -/
theorem jwAnn_mul_fureyVacuumIdempotent (i : Fin 3) :
    jwAnn i * fureyVacuumIdempotent = 0 := by
  fin_cases i <;>
    simp [jwAnn, fureyVacuumIdempotent, Algebra.TensorProduct.tmul_mul_tmul,
      σPlus_mul_N_plus, σ3c_mul_N_plus]

end InfoGeometry.Physics.ColorCARJordanWigner
