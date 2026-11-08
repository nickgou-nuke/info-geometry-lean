/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarProductWordReadout
import InfoGeometry.Algebra.CuntzComplexificationAlgEquiv

/-! Generator twisted cyclicity of the uniform functional on the actual quotient. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge

local notation "φ" => quotientProductFunctional (fun _ => (1 / 2 : ℝ)) (by norm_num)

private theorem uniform_word_value (u v : List Bool) :
    φ (complexStarWordPair u v) =
      if u = v then (1 / 2 : ℂ) ^ u.length else 0 := by
  exact (quotientProductFunctional_uniform_wordPair u v).trans
    (canonicalGaugeState_word u v)

theorem uniform_generator_twisted_S_wordPair (b : Bool) (u v : List Bool) :
    φ (Sℂ b * complexStarWordPair u v) =
      (1 / 2 : ℂ) * φ (complexStarWordPair u v * Sℂ b) := by
  have hleft : Sℂ b * complexStarWordPair u v = complexStarWordPair (b :: u) v := by
    simp [complexStarWordPair, complexStarWord, mul_assoc]
  rw [hleft]
  cases v with
  | nil =>
      have hright : complexStarWordPair u [] * Sℂ b =
          complexStarWordPair (u ++ [b]) [] := by
        simp [complexStarWordPair, complexStarWord_append, complexStarWord]
      rw [hright, uniform_word_value, uniform_word_value]
      simp
  | cons c v =>
      by_cases hcb : c = b
      · subst c
        have hright : complexStarWordPair u (b :: v) * Sℂ b =
            complexStarWordPair u v := by
          simp [complexStarWordPair, complexStarWord,
            StarMul.star_mul, mul_assoc, complexified_ortho]
        rw [hright, uniform_word_value, uniform_word_value]
        by_cases huv : u = v
        · subst v
          simp [pow_succ, mul_comm]
        · simp [huv]
      · have hright : complexStarWordPair u (c :: v) * Sℂ b = 0 := by
          simp [complexStarWordPair, complexStarWord,
            StarMul.star_mul, mul_assoc, complexified_ortho, hcb]
        have hbc : b ≠ c := Ne.symm hcb
        rw [hright, map_zero, uniform_word_value]
        simp [hbc]

theorem uniform_generator_twisted_S (b : Bool) (x : ComplexStarCuntzAlg Bool) :
    φ (Sℂ b * x) = (1 / 2 : ℂ) * φ (x * Sℂ b) := by
  have hx : x ∈ sourceWordPairSpan := by
    rw [sourceWordPair_span_eq_top]
    trivial
  unfold sourceWordPairSpan at hx
  refine Submodule.span_induction
    (p := fun y _ => φ (Sℂ b * y) = (1 / 2 : ℂ) * φ (y * Sℂ b))
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨⟨u, v⟩, rfl⟩
    exact uniform_generator_twisted_S_wordPair b u v
  · simp
  · intro y z _ _ hy hz
    simp only [mul_add, add_mul, map_add]
    rw [hy, hz]
  · intro c y _ hy
    simp only [mul_smul_comm, smul_mul_assoc, map_smul]
    rw [hy]

theorem uniform_generator_twisted_T (b : Bool) (x : ComplexStarCuntzAlg Bool) :
    φ (Tℂ b * x) = (2 : ℂ) * φ (x * Tℂ b) := by
  have hstar (y : ComplexStarCuntzAlg Bool) : star (φ y) = φ (star y) :=
    (quotientProductFunctional_star (fun _ => (1 / 2 : ℝ)) (by norm_num) y).symm
  have h := congrArg (star : ℂ → ℂ) (uniform_generator_twisted_S b (star x))
  simp only [StarMul.star_mul, hstar, star_star, star_Sℂ,
    star_div₀, star_one, star_ofNat] at h
  calc
    φ (Tℂ b * x) = (2 : ℂ) * (φ (Tℂ b * x) * (1 / 2 : ℂ)) := by ring
    _ = (2 : ℂ) * φ (x * Tℂ b) := by rw [← h]

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end
