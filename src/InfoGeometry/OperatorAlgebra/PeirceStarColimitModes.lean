/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.SquareZeroPair
import InfoGeometry.OperatorAlgebra.PeirceCoupling.Algebra

/-!
# Exact double-inner-action modes in the real matrix colimit

The native negative square of the inner action has two stationary modes and
two modes weighted by the full Gram operator. Multiplication of endomorphisms
is composition. The conclusions are ordered operator equations; no scalar
eigenvalue, positivity order, or analytic spectral gap is asserted.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceStarColimitModes

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading
open PeirceSuperoperators

attribute [local instance] LieRing.ofAssociativeRing

local notation "d" => LieAlgebra.ad ℝ Limit

section SquareZero

variable {n : ℕ} (N : Stage n)

local notation "U" => ofStage n N
local notation "V" => star U
local notation "E" => U + V
local notation "J" => U - V
local notation "H" => U * V + V * U
local notation "K" => ⁅U, V⁆

private theorem image_square_zero (hN : N * N = 0) : U * U = 0 :=
  limit_square_zero hN

private theorem star_image_square_zero (hN : N * N = 0) : V * V = 0 := by
  rw [← star_mul, image_square_zero N hN, star_zero]

private theorem sum_commutator_gram (hN : N * N = 0) : ⁅E, H⁆ = 0 := by
  rw [← square_zero_pair_sum_sq (image_square_zero N hN) (star_image_square_zero N hN)]
  change E * (E * E) - (E * E) * E = 0
  noncomm_ring

private theorem sum_commutator_difference (hN : N * N = 0) :
    ⁅E, J⁆ = -(2 • K) := by
  change E * J - J * E = -(2 • K)
  rw [square_zero_pair_sum_mul_sub (image_square_zero N hN) (star_image_square_zero N hN),
    square_zero_pair_sub_mul_sum (image_square_zero N hN) (star_image_square_zero N hN),
    two_nsmul]
  abel

private theorem sum_commutator_bracket (hN : N * N = 0) :
    ⁅E, K⁆ = -(2 • (H * J)) := by
  rw [← lie_skew E K, weighted_lie_sum (image_square_zero N hN) (star_image_square_zero N hN)]

/-- The quadratic Gram operator is stationary under the native negative inner square. -/
theorem neg_ad_sum_sq_apply_gram (hN : N * N = 0) :
    (-(d E * d E) : Module.End ℝ Limit) H = 0 := by
  simp only [LinearMap.neg_apply, Module.End.mul_apply, LieAlgebra.ad_apply]
  rw [sum_commutator_gram N hN, lie_zero, neg_zero]

/-- Every inner square annihilates its own generator. -/
theorem neg_ad_sum_sq_apply_sum :
    (-(d E * d E) : Module.End ℝ Limit) E = 0 := by
  simp only [LinearMap.neg_apply, Module.End.mul_apply, LieAlgebra.ad_apply]
  rw [lie_self, lie_zero, neg_zero]

/-- The difference mode retains the ordered, generally noncentral Gram coefficient. -/
theorem neg_ad_sum_sq_apply_difference (hN : N * N = 0) :
    (-(d E * d E) : Module.End ℝ Limit) J = -(4 • (H * J)) := by
  simp only [LinearMap.neg_apply, Module.End.mul_apply, LieAlgebra.ad_apply]
  rw [sum_commutator_difference N hN, lie_neg, lie_nsmul, sum_commutator_bracket N hN]
  simp only [show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul]
  abel

/-- The commutator mode has the same ordered Gram coefficient. -/
theorem neg_ad_sum_sq_apply_bracket (hN : N * N = 0) :
    (-(d E * d E) : Module.End ℝ Limit) K = -(4 • (H * K)) := by
  have hcomm : E * H = H * E := sub_eq_zero.mp (sum_commutator_gram N hN)
  have hprod : ⁅E, H * J⁆ = H * ⁅E, J⁆ := by
    change E * (H * J) - (H * J) * E = H * (E * J - J * E)
    simp only [mul_sub, ← mul_assoc]
    rw [hcomm]
  simp only [LinearMap.neg_apply, Module.End.mul_apply, LieAlgebra.ad_apply]
  rw [sum_commutator_bracket N hN, lie_neg, lie_nsmul, hprod,
    sum_commutator_difference N hN]
  simp only [show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul, mul_neg, mul_add]
  abel

end SquareZero

section Peirce

variable {n : ℕ} (p a : Stage n)

local notation "U" => ofStage n (component10 p a)
local notation "V" => star U
local notation "E" => U + V
local notation "J" => U - V
local notation "H" => U * V + V * U
local notation "K" => ⁅U, V⁆
local notation "S" => reflection (ofStage n p)

/-- Both actual transported opposite star corners remain square-zero. -/
theorem corner_square_zero (hp : IsStarProjection p) : U * U = 0 ∧ V * V = 0 := by
  have hN : component10 p a * component10 p a = 0 := by
    simpa only [pow_two, component10, complementIdempotent] using
      (corners_sq_zero hp.isIdempotentElem a).1
  exact ⟨image_square_zero _ hN, star_image_square_zero _ hN⟩

/-- An actual upper Peirce corner supplies the required square-zero hypothesis. -/
theorem corner_neg_ad_sq_apply_gram (hp : IsStarProjection p) :
    (-(d E * d E) : Module.End ℝ Limit) H = 0 := by
  apply neg_ad_sum_sq_apply_gram
  simpa only [pow_two, component10, complementIdempotent] using
    (corners_sq_zero hp.isIdempotentElem a).1

theorem corner_neg_ad_sq_apply_difference (hp : IsStarProjection p) :
    (-(d E * d E) : Module.End ℝ Limit) J = -(4 • (H * J)) := by
  apply neg_ad_sum_sq_apply_difference
  simpa only [pow_two, component10, complementIdempotent] using
    (corners_sq_zero hp.isIdempotentElem a).1

theorem corner_neg_ad_sq_apply_bracket (hp : IsStarProjection p) :
    (-(d E * d E) : Module.End ℝ Limit) K = -(4 • (H * K)) := by
  apply neg_ad_sum_sq_apply_bracket
  simpa only [pow_two, component10, complementIdempotent] using
    (corners_sq_zero hp.isIdempotentElem a).1

/-- Reflection reverses the actual transported upper corner and its star as a pair. -/
theorem corner_reflection_odd (hp : IsStarProjection p) : S * E * S = -E := by
  have hstar : star (component10 p a) = component01 p (star a) := by
    simp only [component10, component01, complementIdempotent, star_mul,
      star_sub, star_one, hp.isSelfAdjoint.star_eq, mul_assoc]
  have h := PeirceCoupling.reflection_conjugate_sum hp.isIdempotentElem a (star a)
  rw [← hstar] at h
  simpa [reflection, map_ofNat] using congrArg (ofStage n) h

/-- The difference of opposite star corners belongs to the same odd sector. -/
theorem corner_reflection_difference (hp : IsStarProjection p) : S * J * S = -J := by
  have hstar : star (component10 p a) = component01 p (star a) := by
    simp only [component10, component01, complementIdempotent, star_mul,
      star_sub, star_one, hp.isSelfAdjoint.star_eq, mul_assoc]
  have hneg : component01 p (-star a) = -star (component10 p a) := by
    rw [hstar]
    simp only [component01, mul_neg, neg_mul]
  have h := PeirceCoupling.reflection_conjugate_sum hp.isIdempotentElem a (-star a)
  rw [hneg] at h
  simpa [reflection, sub_eq_add_neg, map_ofNat] using congrArg (ofStage n) h

/-- The reflection converts the full Gram operator into its signed commutator. -/
theorem corner_reflection_mul_gram (hp : IsStarProjection p) : S * H = K := by
  have hstar : star (component10 p a) = component01 p (star a) := by
    simp only [component10, component01, complementIdempotent, star_mul,
      star_sub, star_one, hp.isSelfAdjoint.star_eq, mul_assoc]
  have h := PeirceCoupling.reflection_mul_jordan hp.isIdempotentElem a (star a)
  rw [← hstar] at h
  simpa [reflection, Ring.lie_def, map_ofNat] using congrArg (ofStage n) h

/-- The quadratic Gram operator lies in the fixed sector of the same reflection. -/
theorem corner_reflection_even (hp : IsStarProjection p) : S * H * S = H := by
  have hstar : star (component10 p a) = component01 p (star a) := by
    simp only [component10, component01, complementIdempotent, star_mul,
      star_sub, star_one, hp.isSelfAdjoint.star_eq, mul_assoc]
  let G := component10 p a * component01 p (star a) +
    component01 p (star a) * component10 p a
  have hc : Commute (reflection p) G :=
    even_commutes_reflection hp.isIdempotentElem
      (PeirceCoupling.jordan_mem_even hp.isIdempotentElem a (star a))
  have he : reflection p * G * reflection p = G := by
    rw [hc.eq, mul_assoc, reflection_sq hp.isIdempotentElem, mul_one]
  dsimp only [G] at he
  rw [← hstar] at he
  simpa [reflection, map_ofNat] using congrArg (ofStage n) he

/-- The signed commutator also belongs to the fixed sector of the reflection. -/
theorem corner_reflection_bracket_even (hp : IsStarProjection p) : S * K * S = K := by
  have hstar : star (component10 p a) = component01 p (star a) := by
    simp only [component10, component01, complementIdempotent, star_mul,
      star_sub, star_one, hp.isSelfAdjoint.star_eq, mul_assoc]
  have hc : Commute (reflection p) ⁅component10 p a, component01 p (star a)⁆ :=
    even_commutes_reflection hp.isIdempotentElem
      (PeirceCoupling.lie_mem_even hp.isIdempotentElem a (star a))
  have he : reflection p * ⁅component10 p a, component01 p (star a)⁆ * reflection p =
      ⁅component10 p a, component01 p (star a)⁆ := by
    rw [hc.eq, mul_assoc, reflection_sq hp.isIdempotentElem, mul_one]
  rw [← hstar] at he
  simpa [reflection, Ring.lie_def, map_ofNat] using congrArg (ofStage n) he

/-- The reflection anticommutator is exactly a sum of two ordered star products. -/
theorem corner_reflection_gram (hp : IsStarProjection p) :
    -((S * V * S) * U + U * (S * V * S)) = H := by
  have hstar : star (component10 p a) = component01 p (star a) := by
    simp only [component10, component01, complementIdempotent, star_mul,
      star_sub, star_one, hp.isSelfAdjoint.star_eq, mul_assoc]
  have hzero : component10 p (0 : Stage n) = 0 := by simp [component10]
  have h := PeirceCoupling.reflection_conjugate_sum
    hp.isIdempotentElem (0 : Stage n) (star a)
  rw [hzero, zero_add, ← hstar] at h
  have hV : S * V * S = -V := by
    simpa [reflection, map_ofNat] using congrArg (ofStage n) h
  rw [hV]
  noncomm_ring

end Peirce

end InfoGeometry.OperatorAlgebra.PeirceStarColimitModes
