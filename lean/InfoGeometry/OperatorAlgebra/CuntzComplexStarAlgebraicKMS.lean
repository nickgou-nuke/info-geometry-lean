/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarGeneratorCyclicity
import InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeFlow
import InfoGeometry.Modular.KMSState

/-! Full algebraic twisted cyclicity on the corrected binary Cuntz quotient.
This is an algebraic KMS identity, not an analytic strip or completion theorem. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeFlow
open InfoGeometry.Algebra.CuntzKMSCondition

local notation "φ" => quotientProductFunctional (fun _ => (1 / 2 : ℝ)) (by norm_num)

/-- Twisted cyclic elements are closed under multiplication. -/
theorem twisted_cyclicity_mul {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (f : A →ₗ[R] R) (σ : A →ₐ[R] A) {a c : A}
    (ha : ∀ y, f (a * y) = f (y * σ a))
    (hc : ∀ y, f (c * y) = f (y * σ c)) (y : A) :
    f ((a * c) * y) = f (y * σ (a * c)) := by
  rw [mul_assoc, ha, mul_assoc, hc, map_mul σ a c, mul_assoc]

theorem carrierFlow_imaginary_S (b : Bool) :
    carrierFlow Complex.I (Sℂ b) = (1 / 2 : ℂ) • Sℂ b := by
  have h := modularPhaseComplex_imag 2 (by norm_num) 1
  norm_num [Complex.cpow_neg_one] at h
  rw [carrierFlow_S, h]

theorem carrierFlow_imaginary_T (b : Bool) :
    carrierFlow Complex.I (Tℂ b) = (2 : ℂ) • Tℂ b := by
  have h := modularPhaseComplexInv_imag 2 (by norm_num) 1
  norm_num [Complex.cpow_one] at h
  rw [carrierFlow_T, h]

theorem uniform_twisted_word (u : List Bool) (y : ComplexStarCuntzAlg Bool) :
    φ (complexStarWord u * y) = φ (y * carrierFlow Complex.I (complexStarWord u)) := by
  induction u generalizing y with
  | nil => simp [complexStarWord]
  | cons b u ih =>
      change φ ((Sℂ b * complexStarWord u) * y) =
        φ (y * carrierFlow Complex.I (Sℂ b * complexStarWord u))
      apply twisted_cyclicity_mul φ (carrierFlow Complex.I) _ ih y
      intro z
      rw [carrierFlow_imaginary_S, mul_smul_comm, map_smul]
      exact uniform_generator_twisted_S b z

theorem uniform_twisted_star_word (u : List Bool) (y : ComplexStarCuntzAlg Bool) :
    φ (star (complexStarWord u) * y) =
      φ (y * carrierFlow Complex.I (star (complexStarWord u))) := by
  induction u generalizing y with
  | nil => simp [complexStarWord]
  | cons b u ih =>
      simp only [complexStarWord, StarMul.star_mul, star_Sℂ]
      apply twisted_cyclicity_mul φ (carrierFlow Complex.I) ih _ y
      intro z
      rw [carrierFlow_imaginary_T, mul_smul_comm, map_smul]
      exact uniform_generator_twisted_T b z

theorem uniform_twisted_wordPair (u v : List Bool) (y : ComplexStarCuntzAlg Bool) :
    φ (complexStarWordPair u v * y) =
      φ (y * carrierFlow Complex.I (complexStarWordPair u v)) :=
  twisted_cyclicity_mul φ (carrierFlow Complex.I)
    (uniform_twisted_word u) (uniform_twisted_star_word v) y

/-- Algebraic KMS cyclicity at inverse temperature one for generator energy log 2. -/
theorem uniform_algebraic_KMS :
    InfoGeometry.Modular.KMSState.IsAlgebraicKMS1 φ (carrierFlow Complex.I) := by
  intro x y
  have hx : x ∈ sourceWordPairSpan := by
    rw [sourceWordPair_span_eq_top]
    trivial
  unfold sourceWordPairSpan at hx
  refine Submodule.span_induction
    (p := fun a _ => φ (a * y) = φ (y * carrierFlow Complex.I a))
    ?_ ?_ ?_ ?_ hx
  · rintro a ⟨⟨u, v⟩, rfl⟩
    exact uniform_twisted_wordPair u v y
  · simp
  · intro a b _ _ ha hb
    simp only [add_mul, mul_add, map_add]
    rw [ha, hb]
  · intro c a _ ha
    simp only [smul_mul_assoc, mul_smul_comm, map_smul]
    rw [ha]

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end
