import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Polynomial weights of an involutive operator

For an involution `Γ` in a real operator algebra, the two idempotents
`(1 ± Γ)/2` give the exact sheet decomposition.  The statements below are
polynomial identities in the noncommutative operator ring; no exponential,
limit, or diagonal representation is used.
-/

namespace InfoGeometry.OperatorAlgebra

noncomputable section

section

variable {A : Type*} [Ring A] [Algebra ℚ A]

def projectorPlus (Γ : A) : A := (1 / 2 : ℚ) • (1 + Γ)

def projectorMinus (Γ : A) : A := (1 / 2 : ℚ) • (1 - Γ)

theorem projectorPlus_add_projectorMinus (Γ : A) :
    projectorPlus Γ + projectorMinus Γ = 1 := by
  dsimp [projectorPlus, projectorMinus]
  module

theorem projectorPlus_mul_projectorPlus (Γ : A) (hΓ : Γ * Γ = 1) :
    projectorPlus Γ * projectorPlus Γ = projectorPlus Γ := by
  dsimp [projectorPlus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show (1 / 2 : ℚ) * (1 / 2 : ℚ) = (1 / 4 : ℚ) by norm_num]
  simp only [add_mul, mul_add]
  rw [hΓ]
  norm_num [Algebra.smul_def, add_mul, mul_add, map_inv₀, hΓ]
  abel_nf
  rw [two_smul, two_smul]
  have hq : (algebraMap ℚ A) (1 / 4) +
      (algebraMap ℚ A) (1 / 4) = (algebraMap ℚ A) (1 / 2) := by
    rw [← map_add]
    norm_num
  rw [hq]
  rw [← add_mul, hq]

theorem projectorMinus_mul_projectorMinus (Γ : A) (hΓ : Γ * Γ = 1) :
    projectorMinus Γ * projectorMinus Γ = projectorMinus Γ := by
  dsimp [projectorMinus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show (1 / 2 : ℚ) * (1 / 2 : ℚ) = (1 / 4 : ℚ) by norm_num]
  simp only [sub_mul, mul_sub]
  rw [hΓ]
  norm_num [Algebra.smul_def, sub_mul, mul_sub, map_inv₀, hΓ]
  abel_nf
  have hq : (algebraMap ℚ A) (1 / 4) +
      (algebraMap ℚ A) (1 / 4) = (algebraMap ℚ A) (1 / 2) := by
    rw [← map_add]
    norm_num
  simp only [neg_smul, two_smul]
  rw [hq, ← add_mul, hq]
  simp

theorem projectorPlus_mul_projectorMinus (Γ : A) (hΓ : Γ * Γ = 1) :
    projectorPlus Γ * projectorMinus Γ = 0 := by
  dsimp [projectorPlus, projectorMinus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show (1 / 2 : ℚ) * (1 / 2 : ℚ) = (1 / 4 : ℚ) by norm_num]
  simp only [add_mul, mul_sub]
  rw [hΓ]
  norm_num [Algebra.smul_def, add_mul, mul_sub, map_inv₀, hΓ]
  simp only [mul_add, mul_one]
  abel_nf

theorem projectorMinus_mul_projectorPlus (Γ : A) (hΓ : Γ * Γ = 1) :
    projectorMinus Γ * projectorPlus Γ = 0 := by
  dsimp [projectorPlus, projectorMinus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show (1 / 2 : ℚ) * (1 / 2 : ℚ) = (1 / 4 : ℚ) by norm_num]
  simp only [sub_mul, mul_add]
  rw [hΓ]
  norm_num [Algebra.smul_def, sub_mul, mul_add, map_inv₀, hΓ]

def projectorWeight (Γ : A) (r s : ℚ) : A :=
  r • projectorPlus Γ + s • projectorMinus Γ

theorem AlgHom.map_projectorWeight
    {B : Type*} [Ring B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (Γ : A) (r s : ℚ) :
    φ (projectorWeight Γ r s) = projectorWeight (φ Γ) r s := by
  simp [projectorWeight, projectorPlus, projectorMinus]

theorem projectorWeight_one_one (Γ : A) :
    projectorWeight Γ 1 1 = 1 := by
  dsimp [projectorWeight]
  rw [one_smul, one_smul, projectorPlus_add_projectorMinus]

theorem projectorWeight_one_neg_one (Γ : A) :
    projectorWeight Γ 1 (-1) = Γ := by
  dsimp [projectorWeight, projectorPlus, projectorMinus]
  simp only [one_smul, neg_smul]
  module

theorem projectorWeight_commutes (Γ : A) (r s : ℚ) :
    projectorWeight Γ r s * Γ = Γ * projectorWeight Γ r s := by
  have hplus : projectorPlus Γ * Γ = Γ * projectorPlus Γ := by
    dsimp [projectorPlus]
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    noncomm_ring
  have hminus : projectorMinus Γ * Γ = Γ * projectorMinus Γ := by
    dsimp [projectorMinus]
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    noncomm_ring
  dsimp [projectorWeight]
  rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, mul_smul_comm, hplus, hminus]

theorem projectorWeight_mul (Γ : A) (hΓ : Γ * Γ = 1)
    (r s t u : ℚ) :
    projectorWeight Γ r s * projectorWeight Γ t u =
      projectorWeight Γ (r * t) (s * u) := by
  dsimp [projectorWeight]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [projectorPlus_mul_projectorPlus Γ hΓ,
    projectorPlus_mul_projectorMinus Γ hΓ,
    projectorMinus_mul_projectorPlus Γ hΓ,
    projectorMinus_mul_projectorMinus Γ hΓ]
  simp only [smul_zero, zero_add, add_zero, smul_smul]
  rw [mul_comm t r, mul_comm u s]

end

end

end InfoGeometry.OperatorAlgebra
