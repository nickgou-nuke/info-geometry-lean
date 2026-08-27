import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCGroup
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector

namespace InfoGeometry.Algebra.Zorn.G2PCSeparationNormalization

open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-! Group-theoretic normalization of a PC/Weyl separation equality.

This owner deliberately contains no finite enumeration.  It isolates the
exact cancellation boundary needed by the matrix relative-Weyl argument.
-/

theorem pcWord_inverse (e : PCWordExp) :
    (pcWord e)⁻¹ = pcWord (pcInverse e) := by
  apply inv_eq_of_mul_eq_one_left
  rw [pcWord_mul_pcWord, pcCombine_left_inverse]
  rfl

theorem pc_weyl_equality_normalize_left
    {w₁ w₂ : SplitOctF2Aut} (a c d : PCWordExp)
    (h : pcWord c * w₂ = pcWord a * w₁ * pcWord d) :
    w₂ = pcWord (pcInverse c * a) * w₁ * pcWord d := by
  calc
    w₂ = 1 * w₂ := by simp
    _ = (pcWord (pcInverse c) * pcWord c) * w₂ := by
      rw [pcWord_mul_pcWord, pcCombine_left_inverse]
      rfl
    _ = pcWord (pcInverse c) * (pcWord c * w₂) := by
      simp [mul_assoc]
    _ = pcWord (pcInverse c) * (pcWord a * w₁ * pcWord d) := by
      rw [h]
    _ = (pcWord (pcInverse c) * pcWord a) * w₁ * pcWord d := by
      simp [mul_assoc]
    _ = pcWord (pcInverse c * a) * w₁ * pcWord d := by
      rw [pcWord_mul_pcWord]
      simp [mul_assoc, pcCombine_eq_mul]

theorem pc_weyl_separation_of_normalized
    {w₁ w₂ : SplitOctF2Aut}
    (hsep : ∀ a d : PCWordExp,
      w₂ ≠ pcWord a * w₁ * pcWord d) :
    ∀ a c d : PCWordExp,
      pcWord c * w₂ ≠ pcWord a * w₁ * pcWord d := by
  intro a c d heq
  apply hsep (pcInverse c * a) d
  exact pc_weyl_equality_normalize_left a c d heq

theorem ne_iff_mul_inv_ne_one
    {G : Type*} [Group G] {a b : G} :
    a ≠ b ↔ a * b⁻¹ ≠ 1 := by
  constructor
  · intro hab hab1
    apply hab
    calc
      a = (a * b⁻¹) * b := by simp [mul_assoc]
      _ = 1 * b := by rw [hab1]
      _ = b := one_mul b
  · intro hab hEq
    apply hab
    rw [hEq]
    simp

theorem pc_weyl_separation_iff_normalized_ne_one
    {w₁ w₂ : SplitOctF2Aut}
    (a c d : PCWordExp) :
    pcWord c * w₂ ≠ pcWord a * w₁ * pcWord d ↔
      (pcWord c * w₂) * (pcWord a * w₁ * pcWord d)⁻¹ ≠ 1 := by
  exact ne_iff_mul_inv_ne_one

end InfoGeometry.Algebra.Zorn.G2PCSeparationNormalization
