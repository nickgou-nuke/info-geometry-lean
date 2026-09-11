import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace SarsModularWeakValue

open Complex

abbrev State2 := InfoGeometry.Algebra.FiniteSpin.Vec2C
abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

def cinner (u v : State2) : ℂ := star (u 0) * v 0 + star (u 1) * v 1

def matVec (A : M2C) (v : State2) : State2 := fun i => A i 0 * v 0 + A i 1 * v 1

def weakNumerator (A : M2C) (ψi ψf : State2) : ℂ := cinner ψf (matVec A ψi)

def weakDenominator (ψi ψf : State2) : ℂ := cinner ψf ψi

def weakValue? (A : M2C) (ψi ψf : State2) : Option ℂ :=
  if weakDenominator ψi ψf = 0 then none else some (weakNumerator A ψi ψf / weakDenominator ψi ψf)

@[simp] theorem weak_value_none_of_orthogonal (A : M2C) (ψi ψf : State2)
    (h : weakDenominator ψi ψf = 0) : weakValue? A ψi ψf = none := by
  simp [weakValue?, h]

@[simp] theorem weak_value_some_of_nonorthogonal (A : M2C) (ψi ψf : State2)
    (h : weakDenominator ψi ψf ≠ 0) :
    weakValue? A ψi ψf = some (weakNumerator A ψi ψf / weakDenominator ψi ψf) := by
  simp [weakValue?, h]

def surprisalScalar (x : ℝ) : ℝ := Real.exp x - 1 - x

theorem surprisalScalar_nonneg (x : ℝ) : 0 ≤ surprisalScalar x := by
  unfold surprisalScalar
  linarith [Real.add_one_le_exp x]

theorem surprisalScalar_zero : surprisalScalar 0 = 0 := by
  norm_num [surprisalScalar]

def diag2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, b]

def quad2 (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) : ℝ :=
  v 0 * (A 0 0 * v 0 + A 0 1 * v 1) + v 1 * (A 1 0 * v 0 + A 1 1 * v 1)

def IsPSD2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop := ∀ v : Fin 2 → ℝ, 0 ≤ quad2 A v

theorem diag2_psd_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : IsPSD2 (diag2 a b) := by
  intro v
  unfold quad2 diag2
  simp
  nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]

def modularEntropicDiag (k0 k1 ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diag2 (surprisalScalar (ε * k0)) (surprisalScalar (ε * k1))

theorem modular_entropic_diag_psd (k0 k1 ε : ℝ) : IsPSD2 (modularEntropicDiag k0 k1 ε) := by
  apply diag2_psd_of_nonneg <;> exact surprisalScalar_nonneg _

theorem modular_vacuum_zero : modularEntropicDiag 0 0 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [modularEntropicDiag, diag2, surprisalScalar]

def ket0 : State2 := fun i => if i = 0 then 1 else 0

def ket1 : State2 := fun i => if i = 1 then 1 else 0

def identityWeakOperator : M2C := 1

@[simp] theorem weak_denominator_ket0_ket0 : weakDenominator ket0 ket0 = 1 := by
  norm_num [weakDenominator, cinner, ket0]

@[simp] theorem weak_denominator_ket0_ket1 : weakDenominator ket0 ket1 = 0 := by
  norm_num [weakDenominator, cinner, ket0, ket1]

@[simp] theorem identity_weak_numerator_ket0_ket0 :
    weakNumerator identityWeakOperator ket0 ket0 = 1 := by
  norm_num [weakNumerator, matVec, cinner, identityWeakOperator, ket0]

@[simp] theorem identity_weak_value_ket0_ket0 :
    weakValue? identityWeakOperator ket0 ket0 = some 1 := by
  rw [weak_value_some_of_nonorthogonal identityWeakOperator ket0 ket0]
  · norm_num
  · norm_num

@[simp] theorem identity_weak_value_ket0_ket1 :
    weakValue? identityWeakOperator ket0 ket1 = none := by
  rw [weak_value_none_of_orthogonal identityWeakOperator ket0 ket1]
  norm_num

end SarsModularWeakValue

end noncomputable section
