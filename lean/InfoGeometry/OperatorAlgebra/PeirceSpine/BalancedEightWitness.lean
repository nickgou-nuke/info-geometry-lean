/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralWeyl
import InfoGeometry.OperatorAlgebra.CentralPowerLocalization
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# An eight-dimensional noncommutative Peirce witness

The carrier is the full real matrix ring on `Fin 8`.  A binary projection of
trace four and a square-zero partial isometry produce the support trace
profile `(2,4,2)`.  Two retained binary-diagonal operators have positive
adjoint weight one.  Their product vanishes, while a middle-sector matrix
unit supplies a nonzero ordered length-three path.

The same upper odd matrix unit witnesses failure of denominator centrality
and failure of the integral Weyl conjugation to square to the identity.
These are exact finite matrix statements, without a physical anomaly,
thermodynamic, or Clifford classification claim.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.BalancedEightWitness

open _root_.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge

abbrev Mat := Matrix (Fin 8) (Fin 8) ℝ

/-- The generic star-faithfulness hypotheses hold in the full real matrix ring. -/
theorem matrix_threeSumStarFaithful : ThreeSumStarFaithful Mat := by
  intro A B C h
  have ht := congrArg Matrix.trace h
  simp only [Matrix.trace_add, Matrix.trace_zero, Matrix.star_eq_conjTranspose] at ht
  have ha := (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg
  have hb := (Matrix.posSemidef_conjTranspose_mul_self B).trace_nonneg
  have hc := (Matrix.posSemidef_conjTranspose_mul_self C).trace_nonneg
  have habc := (add_eq_zero_iff_of_nonneg (add_nonneg ha hb) hc).mp ht
  have hab := (add_eq_zero_iff_of_nonneg ha hb).mp habc.1
  exact ⟨Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hab.1,
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hab.2,
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp habc.2⟩

/-- Eight is forced by these specified traces and the ordinary matrix trace.
No uniqueness of the represented algebra or the binary cut is asserted. -/
theorem card_eq_eight_of_trace_balance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι ℝ) (hP : Matrix.trace (P N) = 2)
    (hQ : Matrix.trace (Q N) = 2) (hbal : Matrix.trace (V N + V N - 1) = 0) :
    Fintype.card ι = 8 := by
  have hv : Matrix.trace (V N) = 4 := by
    change Matrix.trace (P N + Q N) = 4
    rw [Matrix.trace_add, hP, hQ]
    norm_num
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one, hv] at hbal
  have hcard : (Fintype.card ι : ℝ) = 8 := by linarith
  exact_mod_cast hcard

/-- Matrix units in the full ambient algebra. -/
def E (i j : Fin 8) : Mat := Matrix.single i j 1

@[simp] theorem E_mul (i j k l : Fin 8) :
    E i j * E k l = if j = k then E i l else 0 := by
  by_cases h : j = k
  · subst k
    simp [E]
  · simp [E, Matrix.single_mul_single_of_ne, h]

@[simp] theorem star_E (i j : Fin 8) : star (E i j) = E j i := by
  simp [E, Matrix.star_eq_conjTranspose]

theorem E_ne_zero (i j : Fin 8) : E i j ≠ 0 := by
  intro h
  have hh := congrArg (fun A : Mat => A i j) h
  norm_num [E] at hh

@[simp] theorem trace_E (i : Fin 8) : Matrix.trace (E i i) = 1 := by
  simp [E]

/-- The prescribed balanced binary cut. -/
def binary : Mat := E 0 0 + E 1 1 + E 2 2 + E 3 3

/-- The ordered transition from two lower coordinates to two upper ones. -/
def seed : Mat := E 0 4 + E 1 5

@[simp] theorem star_seed : star seed = E 4 0 + E 5 1 := by
  simp [seed]

theorem binary_idempotent : binary * binary = binary := by
  norm_num [binary, add_mul, mul_add]

theorem binary_self_adjoint : star binary = binary := by
  simp [binary]

theorem seed_square_zero : seed * seed = 0 := by
  norm_num [seed, add_mul, mul_add]

theorem seed_regular : seed * star seed * seed = seed := by
  norm_num [seed, add_mul, mul_add]

theorem seed_support_idempotent : V seed * V seed = V seed :=
  V_idem seed seed_square_zero seed_regular

theorem seed_is_binary_corner : binary * seed * (1 - binary) = seed := by
  norm_num [binary, seed, add_mul, mul_add, mul_sub, sub_mul]

theorem positive_support : P seed = E 0 0 + E 1 1 := by
  norm_num [P, seed, add_mul, mul_add]

theorem negative_support : Q seed = E 4 4 + E 5 5 := by
  norm_num [Q, seed, add_mul, mul_add]

theorem total_support : V seed = E 0 0 + E 1 1 + (E 4 4 + E 5 5) := by
  change P seed + Q seed = _
  rw [positive_support, negative_support]

/-- The residual zero sector retains four independent coordinates. -/
def residual : Mat := 1 - V seed

private theorem identity_expansion :
    (1 : Mat) = E 0 0 + E 1 1 + E 2 2 + E 3 3 + E 4 4 + E 5 5 + E 6 6 + E 7 7 := by
  have h : (∑ i : Fin 8, E i i) = (1 : Mat) := by
    simpa only [E] using (Matrix.sum_single_one (m := Fin 8) (α := ℝ))
  simpa [Fin.sum_univ_succ, add_assoc] using h.symm

theorem residual_support : residual = E 2 2 + E 3 3 + E 6 6 + E 7 7 := by
  rw [residual, total_support, identity_expansion]
  abel

theorem trace_binary : Matrix.trace binary = 4 := by
  norm_num [binary, Matrix.trace_add]

theorem trace_positive_support : Matrix.trace (P seed) = 2 := by
  rw [positive_support]
  norm_num [Matrix.trace_add]

theorem trace_negative_support : Matrix.trace (Q seed) = 2 := by
  rw [negative_support]
  norm_num [Matrix.trace_add]

theorem trace_total_support : Matrix.trace (V seed) = 4 := by
  rw [total_support]
  norm_num [Matrix.trace_add]

theorem trace_residual : Matrix.trace residual = 4 := by
  norm_num [residual, Matrix.trace_sub, Matrix.trace_one, trace_total_support]

/-- This is ordinary matrix-trace balance of the parity operator. -/
theorem trace_parity_zero : Matrix.trace (V seed + V seed - 1) = 0 := by
  norm_num [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_one, trace_total_support]

theorem upper_residual : binary * residual = E 2 2 + E 3 3 := by
  rw [residual, total_support]
  norm_num [binary, mul_sub, mul_add, add_mul]
  abel

theorem lower_residual : (1 - binary) * residual = residual - (E 2 2 + E 3 3) := by
  rw [sub_mul, one_mul, upper_residual]

/-- An explicit nondegenerate skew pairing on the four-coordinate residual sector. -/
def residualPairing : Mat := E 2 3 - E 3 2 + E 6 7 - E 7 6

theorem residualPairing_skew : star residualPairing = -residualPairing := by
  simp only [residualPairing, star_sub, star_add, star_E]
  abel

/-- Its square is minus the corner identity, not minus the ambient identity. -/
theorem residualPairing_square : residualPairing * residualPairing = -residual := by
  rw [residual_support]
  norm_num [residualPairing, sub_mul, mul_sub, add_mul, mul_add]
  abel

theorem residualPairing_supported :
    residual * residualPairing = residualPairing ∧
      residualPairing * residual = residualPairing := by
  rw [residual_support]
  constructor
  · norm_num [residualPairing, sub_mul, mul_sub, add_mul, mul_add]
  · norm_num [residualPairing, sub_mul, mul_sub, add_mul, mul_add]
    abel

/-- The pairing has no kernel on operators supported on the residual left corner. -/
theorem residualPairing_kernel {X : Mat} (hX : residual * X = X)
    (h : residualPairing * X = 0) : X = 0 := by
  have hh := congrArg (fun Y : Mat => residualPairing * Y) h
  rw [← mul_assoc, residualPairing_square, neg_mul, hX, mul_zero] at hh
  exact neg_eq_zero.mp hh

theorem trace_upper_residual : Matrix.trace (binary * residual) = 2 := by
  rw [upper_residual]
  norm_num [Matrix.trace_add]

theorem trace_lower_residual : Matrix.trace ((1 - binary) * residual) = 2 := by
  rw [lower_residual]
  norm_num [Matrix.trace_sub, Matrix.trace_add, trace_residual]

/-- A binary-even operator in the positive odd grade of the emergent cut. -/
def upperChannel : Mat := E 0 2

/-- The second binary-even positive odd channel. -/
def lowerChannel : Mat := E 6 4

/-- A middle-sector operator coupling the two residual binary sectors. -/
def middleBridge : Mat := E 2 6

theorem upperChannel_ne_zero : upperChannel ≠ 0 := E_ne_zero 0 2

theorem lowerChannel_ne_zero : lowerChannel ≠ 0 := E_ne_zero 6 4

theorem upperChannel_binary_even : binary * upperChannel * binary = upperChannel := by
  norm_num [binary, upperChannel, add_mul, mul_add]

theorem lowerChannel_binary_even :
    (1 - binary) * lowerChannel * (1 - binary) = lowerChannel := by
  norm_num [binary, lowerChannel, add_mul, mul_add, sub_mul, mul_sub]

theorem support_mul_upperChannel : V seed * upperChannel = upperChannel := by
  rw [total_support]
  norm_num [upperChannel, add_mul]

theorem upperChannel_mul_support : upperChannel * V seed = 0 := by
  rw [total_support]
  norm_num [upperChannel, mul_add]

theorem upperChannel_grade_one :
    Sigma seed * upperChannel - upperChannel * Sigma seed = upperChannel := by
  change (P seed - Q seed) * upperChannel - upperChannel * (P seed - Q seed) = _
  rw [positive_support, negative_support]
  norm_num [upperChannel, add_mul, mul_add, sub_mul, mul_sub]

theorem lowerChannel_grade_one :
    Sigma seed * lowerChannel - lowerChannel * Sigma seed = lowerChannel := by
  change (P seed - Q seed) * lowerChannel - lowerChannel * (P seed - Q seed) = _
  rw [positive_support, negative_support]
  norm_num [lowerChannel, add_mul, mul_add, sub_mul, mul_sub]

theorem middleBridge_supported : residual * middleBridge * residual = middleBridge := by
  rw [residual, total_support]
  norm_num [middleBridge, add_mul, mul_add, sub_mul, mul_sub]

theorem channels_square_zero :
    (upperChannel + lowerChannel) * (upperChannel + lowerChannel) = 0 := by
  norm_num [upperChannel, lowerChannel, add_mul, mul_add]

/-- The retained grade-zero bridge supplies a nonzero ordered extreme-grade path. -/
theorem bridged_channel_product : upperChannel * middleBridge * lowerChannel = E 0 4 := by
  norm_num [upperChannel, lowerChannel, middleBridge]

theorem bridged_channel_product_ne_zero : upperChannel * middleBridge * lowerChannel ≠ 0 := by
  rw [bridged_channel_product]
  exact E_ne_zero 0 4

/-- The retained channel and bridge explicitly witness noncommutative multiplication. -/
theorem upperChannel_middleBridge_noncommute :
    upperChannel * middleBridge ≠ middleBridge * upperChannel := by
  simpa [upperChannel, middleBridge] using E_ne_zero 0 6

theorem denominator_mul_upperChannel :
    (1 + V seed) * upperChannel = upperChannel + upperChannel := by
  rw [add_mul, one_mul, support_mul_upperChannel]

theorem upperChannel_mul_denominator : upperChannel * (1 + V seed) = upperChannel := by
  rw [mul_add, mul_one, upperChannel_mul_support, add_zero]

theorem denominator_not_commute_upperChannel :
    (1 + V seed) * upperChannel ≠ upperChannel * (1 + V seed) := by
  intro hh
  rw [denominator_mul_upperChannel, upperChannel_mul_denominator] at hh
  apply upperChannel_ne_zero
  exact add_left_cancel (hh.trans (add_zero upperChannel).symm)

/-- The canonical identity shift ceases to be equivalent after multiplying by
this actual matrix. The unreduced Day quotient therefore has no such ambient
multiplication law. -/
theorem day_multiplication_failure :
    ¬ CentralPowerLocalization.DayRel (1 + V seed)
      (CentralPowerLocalization.dayMul (0, upperChannel) (0, 1))
      (CentralPowerLocalization.dayMul (0, upperChannel) (1, 1 + V seed)) :=
  CentralPowerLocalization.dayMul_not_congruent_of_not_commute
    (matrix_threeSumStarFaithful.one_add_gram_left_injective seed)
    denominator_not_commute_upperChannel

/-- Componentwise star likewise fails on the defining numerator shift. -/
theorem day_star_failure :
    ¬ CentralPowerLocalization.DayRel (1 + V seed)
      (CentralPowerLocalization.dayStar (0, upperChannel))
      (CentralPowerLocalization.dayStar (1, (1 + V seed) * upperChannel)) := by
  intro h
  have hself : star (1 + V seed) = 1 + V seed := by
    simp only [star_add, star_one, V_star]
  exact denominator_not_commute_upperChannel
    ((CentralPowerLocalization.dayStar_numerator_shift_iff (s := 1 + V seed)
      hself (matrix_threeSumStarFaithful.one_add_gram_left_injective seed) upperChannel).mp h).eq

theorem weyl_conjugate_upperChannel :
    W_Bog seed * upperChannel * star (W_Bog seed) = -E 4 2 := by
  rw [star_W_Bog_eq seed seed_square_zero seed_regular,
    W_Bog_eq seed seed_square_zero seed_regular, total_support]
  norm_num [J, seed, upperChannel, sub_mul, mul_sub, add_mul, mul_add]

theorem weyl_conjugate_reverseChannel :
    W_Bog seed * E 4 2 * star (W_Bog seed) = upperChannel := by
  rw [star_W_Bog_eq seed seed_square_zero seed_regular,
    W_Bog_eq seed seed_square_zero seed_regular, total_support]
  norm_num [J, seed, upperChannel, sub_mul, mul_sub, add_mul, mul_add]

/-- The square of the Weyl action changes the sign of this nonzero odd operator. -/
theorem weyl_action_twice_upperChannel :
    W_Bog seed * (W_Bog seed * upperChannel * star (W_Bog seed)) *
        star (W_Bog seed) = -upperChannel := by
  rw [weyl_conjugate_upperChannel, mul_neg, neg_mul, weyl_conjugate_reverseChannel]

theorem weyl_action_twice_ne_upperChannel :
    W_Bog seed * (W_Bog seed * upperChannel * star (W_Bog seed)) *
        star (W_Bog seed) ≠ upperChannel := by
  rw [weyl_action_twice_upperChannel]
  intro h
  have hh := congrArg (fun A : Mat => A 0 2) h
  norm_num [upperChannel, E] at hh

/-- The same sign change is realized by the native ambient star-algebra automorphism. -/
theorem native_weyl_action_twice_upperChannel :
    IntegralWeyl.weylAut seed seed_square_zero seed_support_idempotent
      (IntegralWeyl.weylAut seed seed_square_zero seed_support_idempotent upperChannel) =
      -upperChannel := by
  simpa only [IntegralWeyl.weylAut_apply,
    ← W_Bog_eq seed seed_square_zero seed_regular] using weyl_action_twice_upperChannel

theorem native_weyl_action_twice_ne_upperChannel :
    IntegralWeyl.weylAut seed seed_square_zero seed_support_idempotent
      (IntegralWeyl.weylAut seed seed_square_zero seed_support_idempotent upperChannel) ≠
      upperChannel := by
  simpa only [IntegralWeyl.weylAut_apply,
    ← W_Bog_eq seed seed_square_zero seed_regular] using weyl_action_twice_ne_upperChannel

end InfoGeometry.OperatorAlgebra.PeirceSpine.BalancedEightWitness
