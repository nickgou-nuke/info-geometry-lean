/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ordered transfer matrices for a diffusion–decay column

The generic ring identities retain coefficient order. The real specialization
uses the concentration–flux state `(C, J)` with `J = -B * C'` and
`J' = -rate * storage * C`. Consequently its generator is off diagonal and
its square is `(rate * storage / B) • 1`.

For a nonzero impedance `z`, the explicit hyperbolic transfer has unit
determinant, a same-medium composition law, and the two-sided inverse given
by reversing thickness. Different impedances need not commute. The
identification with the physical generator is conditional on
`k ^ 2 = rate * storage / B`; no experimental parameter or boundary condition
is inferred by these identities. No claim about a matrix exponential or ODE
uniqueness is needed for this finite matrix contract.
-/

noncomputable section

namespace InfoGeometry.Nuclear.DiffusionTransfer

section OrderedRing

variable {R : Type*} [Ring R]

/-- An off-diagonal generator with ordered ring coefficients. -/
def offDiag (p q : R) : Matrix (Fin 2) (Fin 2) R := !![0, p; q, 0]

/-- In a noncommutative ring the two diagonal products remain distinct. -/
theorem offDiag_mul (p₂ q₂ p₁ q₁ : R) :
    offDiag p₂ q₂ * offDiag p₁ q₁ = !![p₂ * q₁, 0; 0, q₂ * p₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiag, Matrix.mul_apply, Fin.sum_univ_two]

/-- Squaring retains `p * q` and `q * p`, without a commutativity hypothesis. -/
theorem offDiag_sq (p q : R) :
    offDiag p q * offDiag p q = !![p * q, 0; 0, q * p] :=
  offDiag_mul p q p q

/-- Matrix multiplication is genuinely noncommutative over every nontrivial
coefficient ring, including a commutative coefficient field. -/
theorem offDiag_noncomm [Nontrivial R] :
    offDiag (1 : R) 0 * offDiag 0 1 ≠ offDiag 0 1 * offDiag (1 : R) 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  simpa [offDiag_mul] using h00

/-- The ordered ring interface has actual noncommuting matrix inhabitants. -/
theorem exists_noncommuting_matrices [Nontrivial R] :
    ∃ A B : Matrix (Fin 2) (Fin 2) R, A * B ≠ B * A :=
  ⟨offDiag 1 0, offDiag 0 1, offDiag_noncomm⟩

/-- Full ordered composition of two equal-diagonal layer matrices. -/
theorem ordered_layer_mul (c₂ p₂ q₂ c₁ p₁ q₁ : R) :
    (!![c₂, p₂; q₂, c₂] : Matrix (Fin 2) (Fin 2) R) * !![c₁, p₁; q₁, c₁] =
      !![c₂ * c₁ + p₂ * q₁, c₂ * p₁ + p₂ * c₁;
         q₂ * c₁ + c₂ * q₁, q₂ * p₁ + c₂ * c₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end OrderedRing

/-- Generator for the real concentration–flux state in one homogeneous layer. -/
def physicalGenerator (B storage rate : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  offDiag (-1 / B) (-rate * storage)

/-- Algebraic square; physical positivity is additional model data. -/
theorem physicalGenerator_sq (B storage rate : ℝ) :
    physicalGenerator B storage rate * physicalGenerator B storage rate =
      (rate * storage / B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [physicalGenerator, offDiag, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, div_eq_mul_inv]
  ring

/-- The attenuation relation identifies the generator's scalar square. -/
theorem physicalGenerator_sq_of_relation (B storage rate k : ℝ)
    (hk : k ^ 2 = rate * storage / B) :
    physicalGenerator B storage rate * physicalGenerator B storage rate =
      k ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [physicalGenerator_sq, hk]

/-- Real transfer at attenuation `k`, impedance `z`, and signed thickness `d`. -/
def transfer (k z d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh (k * d), -Real.sinh (k * d) / z;
     -z * Real.sinh (k * d), Real.cosh (k * d)]

@[simp] theorem transfer_zero (k z : ℝ) : transfer k z 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transfer]

/-- A second layer acts on the left of the first layer's state transfer. -/
theorem transfer_add (k z d₁ d₂ : ℝ) (hz : z ≠ 0) :
    transfer k z (d₁ + d₂) = transfer k z d₂ * transfer k z d₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, Matrix.mul_apply, Fin.sum_univ_two, mul_add,
      Real.cosh_add, Real.sinh_add] <;> field_simp [hz] <;> ring

/-- Negative thickness gives a left inverse. -/
theorem transfer_neg_mul (k z d : ℝ) (hz : z ≠ 0) :
    transfer k z (-d) * transfer k z d = 1 := by
  rw [← transfer_add k z d (-d) hz, add_neg_cancel, transfer_zero]

/-- Negative thickness gives a right inverse. -/
theorem transfer_mul_neg (k z d : ℝ) (hz : z ≠ 0) :
    transfer k z d * transfer k z (-d) = 1 := by
  rw [← transfer_add k z (-d) d hz, neg_add_cancel, transfer_zero]

/-- Every nonzero-impedance transfer has determinant one. -/
theorem transfer_det (k z d : ℝ) (hz : z ≠ 0) :
    (transfer k z d).det = 1 := by
  rw [Matrix.det_fin_two]
  change Real.cosh (k * d) * Real.cosh (k * d) -
    (-Real.sinh (k * d) / z) * (-z * Real.sinh (k * d)) = 1
  calc
    _ = Real.cosh (k * d) ^ 2 - Real.sinh (k * d) ^ 2 := by
      field_simp [hz]
    _ = 1 := Real.cosh_sq_sub_sinh_sq (k * d)

/-- With physical impedance `B * k`, the transfer is the hyperbolic
polynomial in the concentration–flux generator. -/
theorem transfer_eq_generator (B storage rate k d : ℝ)
    (hB : B ≠ 0) (hk : k ≠ 0) (hrel : k ^ 2 = rate * storage / B) :
    transfer k (B * k) d =
      Real.cosh (k * d) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (Real.sinh (k * d) / k) • physicalGenerator B storage rate := by
  have hrate : rate * storage = B * k ^ 2 := by
    calc
      rate * storage = k ^ 2 * B := ((eq_div_iff hB).mp hrel).symm
      _ = B * k ^ 2 := mul_comm _ _
  have hq : -rate * storage = -(B * k ^ 2) := by rw [neg_mul, hrate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, physicalGenerator, offDiag, hq, Matrix.add_apply,
      Matrix.smul_apply] <;> field_simp [hB, hk]

/-- The upper-left commutator entry detects order of different media. -/
theorem transfer_commutator_entry (k₁ z₁ d₁ k₂ z₂ d₂ : ℝ) :
    (transfer k₂ z₂ d₂ * transfer k₁ z₁ d₁ -
      transfer k₁ z₁ d₁ * transfer k₂ z₂ d₂) 0 0 =
      (z₁ / z₂ - z₂ / z₁) * Real.sinh (k₁ * d₁) * Real.sinh (k₂ * d₂) := by
  simp [transfer, Matrix.sub_apply, div_eq_mul_inv]
  ring

/-- Nontrivial layers with unequal squared impedances do not commute.
For physical positive impedances, unequal squares mean unequal impedances. -/
theorem transfer_noncomm (k₁ z₁ d₁ k₂ z₂ d₂ : ℝ)
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (hz : z₁ ^ 2 ≠ z₂ ^ 2)
    (h₁ : k₁ * d₁ ≠ 0) (h₂ : k₂ * d₂ ≠ 0) :
    transfer k₂ z₂ d₂ * transfer k₁ z₁ d₁ ≠
      transfer k₁ z₁ d₁ * transfer k₂ z₂ d₂ := by
  have hratio : z₁ / z₂ ≠ z₂ / z₁ := by
    intro h
    apply hz
    simpa [pow_two] using (div_eq_div_iff hz₂ hz₁).mp h
  have hprod : (z₁ / z₂ - z₂ / z₁) *
      Real.sinh (k₁ * d₁) * Real.sinh (k₂ * d₂) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hratio)
      (Real.sinh_ne_zero.mpr h₁)) (Real.sinh_ne_zero.mpr h₂)
  intro h
  apply hprod
  rw [← transfer_commutator_entry k₁ z₁ d₁ k₂ z₂ d₂, h, sub_self]
  rfl

/-- Two unit-thickness positive layers with impedances one and two give a
closed witness that changing their order changes the actual transfer. -/
theorem positive_layers_noncommute :
    transfer 1 2 1 * transfer 1 1 1 ≠ transfer 1 1 1 * transfer 1 2 1 := by
  apply transfer_noncomm <;> norm_num

/-- The real transport interface contains noncommuting positive layers. -/
theorem exists_noncommuting_transfers :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A ∧
      A = transfer 1 2 1 ∧ B = transfer 1 1 1 :=
  ⟨transfer 1 2 1, transfer 1 1 1, positive_layers_noncommute, rfl, rfl⟩

end InfoGeometry.Nuclear.DiffusionTransfer
