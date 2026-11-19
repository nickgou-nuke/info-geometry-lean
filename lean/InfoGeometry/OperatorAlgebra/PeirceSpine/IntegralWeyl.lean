/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.StarGramRegularity
import InfoGeometry.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge
import InfoGeometry.Core.PeirceGrading
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Integral Weyl conjugation and the Cayley numerator

For a square-zero element of an arbitrary star ring, the Gram support commutes
with the seed, its adjoint, and their difference. The integral element
`1 - V + J` is unitary exactly when the support is idempotent. This constructs
a native star algebra automorphism of the entire ambient ring over `ℤ`.

Three-square star faithfulness turns idempotence of the support into the
partial-isometry identity. Under this hypothesis the integral element is the
existing Steinberg element, its square is the negative support reflection,
and its conjugation reverses every integer commutator weight. Its second
conjugation is reflection conjugation; its fourth conjugation is the identity.
The off-shell Cayley numerator has both Gram products equal to `(1 + V)^2`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralWeyl

open _root_.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge
open InfoGeometry.Core.PeirceGrading

variable {B : Type*} [Ring B] [StarRing B]

/-- The support centralizes the seed before any normalization assumption. -/
theorem support_commute_seed {N : B} (hN : N * N = 0) : Commute (V N) N := by
  change (N * star N + star N * N) * N = N * (N * star N + star N * N)
  rw [add_mul, mul_add, mul_assoc (star N) N N, ← mul_assoc N N (star N)]
  simp only [hN, mul_zero, zero_mul, add_zero, zero_add, mul_assoc]

theorem support_commute_star_seed {N : B} (hN : N * N = 0) :
    Commute (V N) (star N) := by
  change V N * star N = star N * V N
  simpa only [star_mul, V_star] using
    (congrArg star (support_commute_seed hN).eq).symm

theorem support_commute_rotor {N : B} (hN : N * N = 0) : Commute (V N) (J N) := by
  change V N * (N - star N) = (N - star N) * V N
  simp only [mul_sub, sub_mul, (support_commute_seed hN).eq,
    (support_commute_star_seed hN).eq]

/-- Faithfulness discharges the partial-isometry hypothesis of the existing bridge. -/
theorem regular_of_support_idempotent (hF : ThreeSumStarFaithful B) {N : B}
    (hN : N * N = 0) (hV : V N * V N = V N) : N * star N * N = N := by
  have hz : N * (1 - V N) = 0 := by
    apply (hF (N * (1 - V N)) (star N * (1 - V N)) 0 ?_).1
    calc
      _ = (1 - V N) * V N * (1 - V N) := by
        simp only [star_mul, star_sub, star_one, V_star, star_star,
          star_zero, mul_zero, add_zero]
        unfold V
        noncomm_ring
      _ = 0 := by rw [sub_mul, one_mul, hV, sub_self, zero_mul]
  have hNV : N * V N = N :=
    (sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using hz)).symm
  calc
    N * star N * N = N * V N := by
      unfold V
      rw [mul_add, ← mul_assoc N N (star N), hN, zero_mul, zero_add, mul_assoc]
    _ = N := hNV

/-- Both Gram defects of the integral element are exactly the support defect. -/
theorem integral_gram_defects {N : B} (hN : N * N = 0) :
    star (1 - V N + J N) * (1 - V N + J N) = 1 + (V N * V N - V N) ∧
      (1 - V N + J N) * star (1 - V N + J N) = 1 + (V N * V N - V N) := by
  have hcomm := (support_commute_rotor hN).eq
  have hJ := J_sq_eq_neg_V N hN
  constructor <;>
    (simp only [star_add, star_sub, star_one, V_star, J_star,
      add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, neg_mul, mul_neg,
      hcomm, hJ]
     abel)

theorem integral_mem_unitary_iff {N : B} (hN : N * N = 0) :
    1 - V N + J N ∈ unitary B ↔ V N * V N = V N := by
  change (star (1 - V N + J N) * (1 - V N + J N) = 1 ∧
    (1 - V N + J N) * star (1 - V N + J N) = 1) ↔ _
  rw [(integral_gram_defects hN).1, (integral_gram_defects hN).2]
  constructor
  · intro h
    exact sub_eq_zero.mp (add_left_cancel (h.1.trans (add_zero (1 : B)).symm))
  · intro hV
    simp only [hV, sub_self, add_zero, and_self]

/-- The native unitary needs idempotence of the support, without faithfulness. -/
def weylUnitary (N : B) (hN : N * N = 0) (hV : V N * V N = V N) : unitary B :=
  ⟨1 - V N + J N, (integral_mem_unitary_iff hN).mpr hV⟩

@[simp] theorem coe_weylUnitary (N : B) (hN : N * N = 0)
    (hV : V N * V N = V N) :
    (weylUnitary N hN hV : B) = 1 - V N + J N := rfl

/-- Conjugation is Mathlib's native star algebra automorphism over the integers. -/
def weylAut (N : B) (hN : N * N = 0) (hV : V N * V N = V N) : B ≃⋆ₐ[ℤ] B :=
  Unitary.conjStarAlgAut ℤ B (weylUnitary N hN hV)

@[simp] theorem weylAut_apply (N : B) (hN : N * N = 0)
    (hV : V N * V N = V N) (X : B) :
    weylAut N hN hV X = (1 - V N + J N) * X * star (1 - V N + J N) := rfl

/-- The polynomial agrees with the already owned Steinberg element on shell. -/
theorem weyl_eq_steinberg {N : B} (hN : N * N = 0)
    (hregular : N * star N * N = N) :
    1 - V N + J N = W_Bog N := (W_Bog_eq N hN hregular).symm

theorem weylAut_sigma (hF : ThreeSumStarFaithful B) {N : B}
    (hN : N * N = 0) (hV : V N * V N = V N) :
    weylAut N hN hV (Sigma N) = -Sigma N := by
  have hr := regular_of_support_idempotent hF hN hV
  simpa only [weylAut_apply, ← W_Bog_eq N hN hr] using W_Bog_conj_Sigma N hN hr

/-- The integral element squares to the negative reflection, not generally to one. -/
theorem integral_square {N : B} (hN : N * N = 0)
    (hregular : N * star N * N = N) :
    (1 - V N + J N) * (1 - V N + J N) = 1 - (V N + V N) := by
  have hVJ : V N * J N = J N := by
    simp only [J, mul_sub, V_mul_N_plus N hN hregular,
      V_mul_star_N_plus N hN hregular]
  have hJV : J N * V N = J N := by
    simp only [J, sub_mul, N_plus_mul_V N hN hregular,
      star_N_plus_mul_V N hN hregular]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    V_idem N hN hregular, hVJ, hJV, J_sq_eq_neg_V N hN]
  abel

theorem integral_fourth_power {N : B} (hN : N * N = 0)
    (hregular : N * star N * N = N) : (1 - V N + J N) ^ 4 = 1 := by
  have href : 1 - (V N + V N) = -reflection (V N) := by
    unfold reflection
    noncomm_ring
  calc
    _ = ((1 - V N + J N) * (1 - V N + J N)) *
        ((1 - V N + J N) * (1 - V N + J N)) := by noncomm_ring
    _ = (1 - (V N + V N)) * (1 - (V N + V N)) := by
      rw [integral_square hN hregular]
    _ = 1 := by
      rw [href, neg_mul, mul_neg, neg_neg, reflection_sq (V_idem N hN hregular)]

/-- Twice conjugating gives the existing support-reflection action on all of `B`. -/
theorem weylAut_twice (hF : ThreeSumStarFaithful B) {N : B}
    (hN : N * N = 0) (hV : V N * V N = V N) (X : B) :
    weylAut N hN hV (weylAut N hN hV X) =
      reflection (V N) * X * reflection (V N) := by
  have hs := integral_square hN (regular_of_support_idempotent hF hN hV)
  have hstar : star (1 - V N + J N) * star (1 - V N + J N) =
      1 - (V N + V N) := by
    simpa only [star_mul, star_sub, star_one, star_add, V_star] using congrArg star hs
  calc
    _ = ((1 - V N + J N) * (1 - V N + J N)) * X *
        (star (1 - V N + J N) * star (1 - V N + J N)) := by
      simp only [weylAut_apply, mul_assoc]
    _ = (1 - (V N + V N)) * X * (1 - (V N + V N)) := by rw [hs, hstar]
    _ = reflection (V N) * X * reflection (V N) := by
      unfold reflection
      noncomm_ring

theorem weylAut_four_times (hF : ThreeSumStarFaithful B) {N : B}
    (hN : N * N = 0) (hV : V N * V N = V N) (X : B) :
    weylAut N hN hV (weylAut N hN hV
      (weylAut N hN hV (weylAut N hN hV X))) = X := by
  rw [weylAut_twice hF hN hV, weylAut_twice hF hN hV]
  calc
    _ = (reflection (V N) * reflection (V N)) * X *
        (reflection (V N) * reflection (V N)) := by noncomm_ring
    _ = X := by rw [reflection_sq hV, one_mul, mul_one]

/-- Every integral commutator weight changes sign under the Weyl automorphism. -/
theorem weylAut_reverses_weight (hF : ThreeSumStarFaithful B) {N : B}
    (hN : N * N = 0) (hV : V N * V N = V N) (k : ℤ) {X : B}
    (hX : Sigma N * X - X * Sigma N = k • X) :
    Sigma N * weylAut N hN hV X - weylAut N hN hV X * Sigma N =
      (-k) • weylAut N hN hV X := by
  calc
    _ = -(weylAut N hN hV (Sigma N * X - X * Sigma N)) := by
      simp only [map_sub, map_mul, weylAut_sigma hF hN hV]
      noncomm_ring
    _ = -(k • weylAut N hN hV X) := by rw [hX, map_zsmul]
    _ = (-k) • weylAut N hN hV X := by rw [neg_zsmul]

/-- The Cayley numerator has equal two-sided Gram products, also off shell. -/
theorem cayley_numerator_grams {N : B} (hN : N * N = 0) :
    star (1 - V N + (J N + J N)) * (1 - V N + (J N + J N)) =
        (1 + V N) * (1 + V N) ∧
      (1 - V N + (J N + J N)) * star (1 - V N + (J N + J N)) =
        (1 + V N) * (1 + V N) := by
  have hcomm := (support_commute_rotor hN).eq
  have hJ := J_sq_eq_neg_V N hN
  constructor <;>
    (simp only [star_add, star_sub, star_one, V_star, J_star,
      add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, neg_mul, mul_neg,
      hcomm, hJ]
     abel)

/-- On shell the Cayley numerator is the denominator times the integral element. -/
theorem cayley_numerator_on_shell {N : B} (hN : N * N = 0)
    (hregular : N * star N * N = N) :
    (1 + V N) * (1 - V N + J N) = 1 - V N + (J N + J N) := by
  have hVJ : V N * J N = J N := by
    simp only [J, mul_sub, V_mul_N_plus N hN hregular,
      V_mul_star_N_plus N hN hregular]
  simp only [mul_add, add_mul, mul_sub, mul_one, one_mul,
    V_idem N hN hregular, hVJ]
  abel

end InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralWeyl
