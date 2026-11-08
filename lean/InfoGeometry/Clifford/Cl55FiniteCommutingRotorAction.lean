import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-! A finite two-channel rotor action.

This owner proves only the algebraic rank-two closure.  It does not assert
maximality, a Spin-group identification, or an architectural interpretation.
-/

noncomputable section

namespace InfoGeometry.Clifford.FiniteCommutingRotorAction

variable {A : Type*} [Ring A] [Algebra ℝ A]

def rotor (B : A) (theta : ℝ) : A :=
  (Real.cos theta) • (1 : A) + (Real.sin theta) • B

theorem rotor_zero (B : A) : rotor B 0 = 1 := by
  unfold rotor
  simp

theorem rotor_add (B : A) (hB : B * B = -(1 : A)) (s t : ℝ) :
    rotor B (s + t) = rotor B s * rotor B t := by
  unfold rotor
  rw [Real.cos_add, Real.sin_add]
  rw [add_mul, mul_add, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    smul_smul, hB, smul_neg, sub_smul, add_smul]
  simp only [mul_comm (Real.cos t), mul_comm (Real.sin t)]
  abel

theorem rotor_commute (B C : A) (hBC : B * C = C * B) (s t : ℝ) :
    rotor B s * rotor C t = rotor C t * rotor B s := by
  unfold rotor
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    smul_smul]
  rw [hBC]
  module

def rankTwoRotor (B C : A) (s t : ℝ) : A := rotor B s * rotor C t

theorem rankTwoRotor_add
    (B C : A) (hB : B * B = -(1 : A)) (hC : C * C = -(1 : A))
    (hBC : B * C = C * B) (s₁ s₂ t₁ t₂ : ℝ) :
    rankTwoRotor B C (s₁ + s₂) (t₁ + t₂) =
      rankTwoRotor B C s₁ t₁ * rankTwoRotor B C s₂ t₂ := by
  unfold rankTwoRotor
  rw [rotor_add B hB, rotor_add C hC]
  calc
    rotor B s₁ * rotor B s₂ * (rotor C t₁ * rotor C t₂) =
        rotor B s₁ * (rotor B s₂ * rotor C t₁) * rotor C t₂ := by
          simp only [mul_assoc]
    _ = rotor B s₁ * (rotor C t₁ * rotor B s₂) * rotor C t₂ := by
          rw [rotor_commute B C hBC s₂ t₁]
    _ = (rotor B s₁ * rotor C t₁) *
        (rotor B s₂ * rotor C t₂) := by
          simp only [mul_assoc]

theorem rankTwoRotor_inverse
    (B C : A) (hB : B * B = -(1 : A)) (hC : C * C = -(1 : A))
    (hBC : B * C = C * B) (s t : ℝ) :
    rankTwoRotor B C s t * rankTwoRotor B C (-s) (-t) = 1 := by
  unfold rankTwoRotor
  calc
    (rotor B s * rotor C t) * (rotor B (-s) * rotor C (-t)) =
        rotor B s * (rotor C t * rotor B (-s)) * rotor C (-t) := by
          simp only [mul_assoc]
    _ = rotor B s * (rotor B (-s) * rotor C t) * rotor C (-t) := by
          rw [rotor_commute C B hBC.symm t (-s)]
    _ = (rotor B s * rotor B (-s)) *
        (rotor C t * rotor C (-t)) := by
          simp only [mul_assoc]
    _ = 1 := by
          rw [← rotor_add B hB, ← rotor_add C hC]
          simp [rotor_zero]

theorem rankTwoRotor_relative
    (B C : A) (hB : B * B = -(1 : A)) (hC : C * C = -(1 : A))
    (hBC : B * C = C * B) (s t u v : ℝ) :
    rankTwoRotor B C (-s) (-t) * rankTwoRotor B C u v =
      rankTwoRotor B C (u - s) (v - t) := by
  have h := rankTwoRotor_add B C hB hC hBC (-s) u (-t) v
  rw [add_comm (-s) u, add_comm (-t) v] at h
  exact h.symm

end InfoGeometry.Clifford.FiniteCommutingRotorAction
