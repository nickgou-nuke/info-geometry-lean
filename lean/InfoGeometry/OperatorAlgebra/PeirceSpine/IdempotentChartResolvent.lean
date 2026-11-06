/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Idempotent charts and the two Peirce resolvents

The existing Peirce corners and unipotent conjugations are retained. The
positive upper chart uses `conjPlusInv`, whereas `conjPlus` has the opposite
linear sign. Its action on the positive lower chart is the exact idempotent
`P + Φ - Σ - V N₊`.

The inverse formulas use Mathlib's `Ring.inverse` on genuine units. A unit
`1 - V` supplies both corner denominator units because those denominators
commute and their product is `1 - V`. The final sandwich identity applies to
every upper-corner variation, without commuting it with the background
resolvents. These are identities in an associative ring; differentiability,
a manifold atlas, and a metric are separate constructions.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- The positive upper graph is the existing upper graph with negated
parameter. Its sign agrees with conjugation by `1 - N₊` on the left. -/
theorem add_conePlus_idempotent {P : B} (hP : P * P = P) (A : B) :
    (P + conePlus P A) * (P + conePlus P A) = P + conePlus P A := by
  simpa only [InfoGeometry.Core.IdempotentGraphReflectionOrder.upperGraph,
    InfoGeometry.Core.IdempotentGraphReflectionOrder.upperCorner, conePlus,
    mul_neg, neg_mul, sub_neg_eq_add] using
    InfoGeometry.Core.IdempotentGraphReflectionOrder.upperGraph_idempotent hP (-A)

/-- The positive lower graph is the existing lower graph. -/
theorem add_coneMinus_idempotent {P : B} (hP : P * P = P) (C : B) :
    (P + coneMinus P C) * (P + coneMinus P C) = P + coneMinus P C := by
  exact InfoGeometry.Core.IdempotentGraphReflectionOrder.lowerGraph_idempotent hP C

/-- Inverting the existing upper shear gives the positive chart. -/
theorem conjPlusInv_idempotent_point_form {P : B} (hP : P * P = P) (A : B) :
    conjPlusInv P A P = P + conePlus P A := by
  simpa only [conjPlus, conjPlusInv, projChartPlus, conePlus_neg,
    add_neg_eq_sub, sub_neg_eq_add] using
    conjPlus_idempotent_point_form hP (-A)

/-- Adding both tangent corners has exactly the quadratic Peirce defect.
The defect is not asserted to be nonzero. -/
theorem idempotencyDefect_add_genPhi {P : B} (hP : P * P = P) (A C : B) :
    idempotencyDefect (P + genPhi P A C) = genV P A C := by
  have hcross : P * genPhi P A C + genPhi P A C * P = genPhi P A C := by
    peirce_nf hP
  calc
    idempotencyDefect (P + genPhi P A C) = genPhi P A C * genPhi P A C :=
      idempotencyDefect_idempotent_add_of_cross_sum hP hcross
    _ = genV P A C :=
      (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1

/-- Linear addition remains on the idempotent locus exactly when its
quadratic defect vanishes. -/
theorem add_genPhi_idempotent_iff {P : B} (hP : P * P = P) (A C : B) :
    (P + genPhi P A C) * (P + genPhi P A C) = P + genPhi P A C ↔
      genV P A C = 0 := by
  rw [← idempotencyDefect_eq_zero_iff, idempotencyDefect_add_genPhi hP]

/-- The commutator retains both the even oriented cycle and the odd chart
displacements. -/
theorem positive_chart_commutator {P : B} (hP : P * P = P) (A C : B) :
    comm (P + conePlus P A) (P + coneMinus P C) =
      genSig P A C - genPhi P A C := by
  peirce_nf hP

/-- Both positive chart displacements must vanish if the chart points
commute. This criterion holds in every characteristic. -/
theorem positive_chart_commutator_eq_zero_iff {P : B} (hP : P * P = P) (A C : B) :
    comm (P + conePlus P A) (P + coneMinus P C) = 0 ↔
      conePlus P A = 0 ∧ coneMinus P C = 0 := by
  constructor
  · intro h
    have hplus : P * comm (P + conePlus P A) (P + coneMinus P C) * (1 - P) =
        -conePlus P A := by
      peirce_nf hP
    have hminus : (1 - P) * comm (P + conePlus P A) (P + coneMinus P C) * P =
        -coneMinus P C := by
      peirce_nf hP
    rw [h, mul_zero, zero_mul] at hplus hminus
    exact ⟨neg_eq_zero.mp hplus.symm, neg_eq_zero.mp hminus.symm⟩
  · rintro ⟨hplus, hminus⟩
    simp only [hplus, hminus, add_zero, comm, sub_self]

/-- The corrected ordered two-chart conjugate stays on the idempotent
locus by the existing conjugation covariance of the defect. -/
theorem conjPlusInv_lower_chart_idempotent {P : B} (hP : P * P = P) (A C : B) :
    conjPlusInv P A (P + coneMinus P C) * conjPlusInv P A (P + coneMinus P C) =
      conjPlusInv P A (P + coneMinus P C) := by
  have hcancel : (1 + conePlus P A) * (1 - conePlus P A) = 1 := by
    peirce_nf hP
  have hlower : idempotencyDefect (P + coneMinus P C) = 0 :=
    idempotencyDefect_eq_zero_iff.mpr (add_coneMinus_idempotent hP C)
  apply idempotencyDefect_eq_zero_iff.mp
  unfold conjPlusInv
  rw [idempotencyDefect_conj _ _ _ hcancel, hlower, mul_zero, zero_mul]

/-- Read the existing ordered Bruhat orbit at the two negated parameters.
The quadratic correction is `-Σ`, and the cubic correction is `-V N₊`. -/
theorem conjPlusInv_lower_chart_eq {P : B} (hP : P * P = P) (A C : B) :
    conjPlusInv P A (P + coneMinus P C) =
      P + genPhi P A C - genSig P A C - genV P A C * conePlus P A := by
  have hexpand :=
    (moebius_bruhat_idempotent_orbit_and_metric_invariance hP (-A) (-C)).2.2
  calc
    conjPlusInv P A (P + coneMinus P C) =
        ((1 + conePlus P (-A)) * (1 - coneMinus P (-C))) * P *
          ((1 + coneMinus P (-C)) * (1 - conePlus P (-A))) := by
      simp only [conjPlusInv, conePlus_neg, coneMinus_neg,
        add_neg_eq_sub, sub_neg_eq_add]
      peirce_nf hP
    _ = P - genJ P (-A) (-C) - genSig P (-A) (-C) +
        genV P (-A) (-C) * conePlus P (-A) - (2 : ℤ) • coneMinus P (-C) := hexpand
    _ = P + genPhi P A C - genSig P A C - genV P A C * conePlus P A := by
      peirce_nf hP

/-- Native product-power intertwining, including degree zero. -/
theorem qgtPlus_pow_mul_conePlus (P A C : B) (n : ℕ) :
    qgtPlus P A C ^ n * conePlus P A = conePlus P A * qgtMinus P A C ^ n := by
  exact mul_pow_mul (conePlus P A) (coneMinus P C) n

/-- The lower-sheet version of product-power intertwining. -/
theorem qgtMinus_pow_mul_coneMinus (P A C : B) (n : ℕ) :
    qgtMinus P A C ^ n * coneMinus P C = coneMinus P C * qgtPlus P A C ^ n := by
  exact mul_pow_mul (coneMinus P C) (conePlus P A) n

/-- On the chosen upper generator, powers of the full cycle restrict to
the upper cycle. -/
theorem genV_pow_mul_conePlus {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    genV P A C ^ n * conePlus P A = qgtPlus P A C ^ n * conePlus P A := by
  have hshift : SemiconjBy (conePlus P A) (qgtMinus P A C) (genV P A C) := by
    change conePlus P A * qgtMinus P A C = genV P A C * conePlus P A
    simp only [qgtMinus]
    peirce_nf hP
  exact (hshift.pow_right n).eq.symm.trans (qgtPlus_pow_mul_conePlus P A C n).symm

/-- On the chosen lower generator, powers of the full cycle restrict to
the lower cycle. -/
theorem genV_pow_mul_coneMinus {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    genV P A C ^ n * coneMinus P C = qgtMinus P A C ^ n * coneMinus P C := by
  have hshift : SemiconjBy (coneMinus P C) (qgtPlus P A C) (genV P A C) := by
    change coneMinus P C * qgtPlus P A C = genV P A C * coneMinus P C
    simp only [qgtPlus]
    peirce_nf hP
  exact (hshift.pow_right n).eq.symm.trans (qgtMinus_pow_mul_coneMinus P A C n).symm

/-- The two corner denominators commute because the two cycles are
orthogonal in both orders. -/
theorem qgt_complements_commute {P : B} (hP : P * P = P) (A C : B) :
    Commute (1 - qgtPlus P A C) (1 - qgtMinus P A C) := by
  rcases qgt_cycles_orthogonal hP A C with ⟨hpm, hmp⟩
  change (1 - qgtPlus P A C) * (1 - qgtMinus P A C) =
    (1 - qgtMinus P A C) * (1 - qgtPlus P A C)
  noncomm_ring [hpm, hmp]

/-- A unit full denominator is equivalent to two genuine corner
denominator units. No inverse is postulated as an extra structure field. -/
theorem isUnit_one_sub_genV_iff_corner_units {P : B} (hP : P * P = P) (A C : B) :
    IsUnit (1 - genV P A C) ↔
      IsUnit (1 - qgtPlus P A C) ∧ IsUnit (1 - qgtMinus P A C) := by
  rw [← chart_corner_complement_product hP A C]
  exact (qgt_complements_commute hP A C).isUnit_mul_iff

/-- The inverse reverses the two ordered denominator factors. -/
theorem ringInverse_one_sub_genV_factorization {P : B} (hP : P * P = P) (A C : B)
    (hunit : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) =
      Ring.inverse (1 - qgtMinus P A C) * Ring.inverse (1 - qgtPlus P A C) := by
  have hplus := ((isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit).1
  rw [← chart_corner_complement_product hP A C]
  exact Ring.inverse_mul (Or.inl hplus)

/-- The two genuine corner inverses intertwine across the upper
generator, retaining their left/right order. -/
theorem ringInverse_one_sub_qgtPlus_mul_conePlus {P : B} (hP : P * P = P) (A C : B)
    (hunit : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - qgtPlus P A C) * conePlus P A =
      conePlus P A * Ring.inverse (1 - qgtMinus P A C) := by
  rcases (isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit with ⟨hplus, hminus⟩
  have hshift : (1 - qgtPlus P A C) * conePlus P A =
      conePlus P A * (1 - qgtMinus P A C) := by
    simp only [qgtPlus, qgtMinus]
    noncomm_ring
  apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hplus).mpr
  rw [← mul_assoc, hshift, mul_assoc, Ring.mul_inverse_cancel _ hminus, mul_one]

/-- The lower generator intertwines in the opposite direction. -/
theorem ringInverse_one_sub_qgtMinus_mul_coneMinus {P : B} (hP : P * P = P) (A C : B)
    (hunit : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - qgtMinus P A C) * coneMinus P C =
      coneMinus P C * Ring.inverse (1 - qgtPlus P A C) := by
  rcases (isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit with ⟨hplus, hminus⟩
  have hshift : (1 - qgtMinus P A C) * coneMinus P C =
      coneMinus P C * (1 - qgtPlus P A C) := by
    simp only [qgtPlus, qgtMinus]
    noncomm_ring
  apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hminus).mpr
  rw [← mul_assoc, hshift, mul_assoc, Ring.mul_inverse_cancel _ hplus, mul_one]

/-- Left restriction of the full inverse to any upper-corner variation.
The variation need not equal the background upper generator. -/
theorem ringInverse_one_sub_genV_mul_conePlus {P : B} (hP : P * P = P) (A C X : B)
    (hunit : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) * conePlus P X =
      Ring.inverse (1 - qgtPlus P A C) * conePlus P X := by
  have hplus := ((isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit).1
  have hfactor : (1 - qgtMinus P A C) * (1 - qgtPlus P A C) = 1 - genV P A C :=
    (qgt_complements_commute hP A C).eq.symm.trans (chart_corner_complement_product hP A C)
  apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hunit).mpr
  calc
    conePlus P X = (1 - qgtMinus P A C) * conePlus P X := by
      simp only [qgtMinus]
      peirce_nf hP
    _ = (1 - qgtMinus P A C) *
        ((1 - qgtPlus P A C) * (Ring.inverse (1 - qgtPlus P A C) * conePlus P X)) := by
      rw [Ring.mul_inverse_cancel_left _ _ hplus]
    _ = (1 - genV P A C) * (Ring.inverse (1 - qgtPlus P A C) * conePlus P X) := by
      rw [← mul_assoc, hfactor]

/-- Right restriction of the full inverse to any upper-corner variation. -/
theorem conePlus_mul_ringInverse_one_sub_genV {P : B} (hP : P * P = P) (A C X : B)
    (hunit : IsUnit (1 - genV P A C)) :
    conePlus P X * Ring.inverse (1 - genV P A C) =
      conePlus P X * Ring.inverse (1 - qgtMinus P A C) := by
  have hminus := ((isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit).2
  have hfactor : (1 - qgtMinus P A C) * (1 - qgtPlus P A C) = 1 - genV P A C :=
    (qgt_complements_commute hP A C).eq.symm.trans (chart_corner_complement_product hP A C)
  symm
  apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ hunit).mpr
  calc
    (conePlus P X * Ring.inverse (1 - qgtMinus P A C)) * (1 - genV P A C) =
        conePlus P X * (Ring.inverse (1 - qgtMinus P A C) * (1 - qgtMinus P A C)) *
          (1 - qgtPlus P A C) := by
      rw [← hfactor]
      simp only [mul_assoc]
    _ = conePlus P X * (1 - qgtPlus P A C) := by
      rw [Ring.inverse_mul_cancel _ hminus, mul_one]
    _ = conePlus P X := by
      simp only [qgtPlus]
      peirce_nf hP

/-- Left restriction of the full inverse to any lower-corner variation. -/
theorem ringInverse_one_sub_genV_mul_coneMinus {P : B} (hP : P * P = P) (A C X : B)
    (hunit : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) * coneMinus P X =
      Ring.inverse (1 - qgtMinus P A C) * coneMinus P X := by
  have hminus := ((isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit).2
  apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hunit).mpr
  calc
    coneMinus P X = (1 - qgtPlus P A C) * coneMinus P X := by
      simp only [qgtPlus]
      peirce_nf hP
    _ = (1 - qgtPlus P A C) *
        ((1 - qgtMinus P A C) * (Ring.inverse (1 - qgtMinus P A C) * coneMinus P X)) := by
      rw [Ring.mul_inverse_cancel_left _ _ hminus]
    _ = (1 - genV P A C) * (Ring.inverse (1 - qgtMinus P A C) * coneMinus P X) := by
      rw [← mul_assoc, chart_corner_complement_product hP A C]

/-- Right restriction of the full inverse to any lower-corner variation. -/
theorem coneMinus_mul_ringInverse_one_sub_genV {P : B} (hP : P * P = P) (A C X : B)
    (hunit : IsUnit (1 - genV P A C)) :
    coneMinus P X * Ring.inverse (1 - genV P A C) =
      coneMinus P X * Ring.inverse (1 - qgtPlus P A C) := by
  have hplus := ((isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit).1
  symm
  apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ hunit).mpr
  calc
    (coneMinus P X * Ring.inverse (1 - qgtPlus P A C)) * (1 - genV P A C) =
        coneMinus P X * (Ring.inverse (1 - qgtPlus P A C) * (1 - qgtPlus P A C)) *
          (1 - qgtMinus P A C) := by
      rw [← chart_corner_complement_product hP A C]
      simp only [mul_assoc]
    _ = coneMinus P X * (1 - qgtMinus P A C) := by
      rw [Ring.inverse_mul_cancel _ hplus, mul_one]
    _ = coneMinus P X := by
      simp only [qgtMinus]
      peirce_nf hP

/-- The full resolvent sandwich equals the two-sheet sandwich on an
arbitrary upper variation, with the displayed factor order. -/
theorem ringInverse_genV_sandwich_conePlus {P : B} (hP : P * P = P) (A C X : B)
    (hunit : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) * conePlus P X * Ring.inverse (1 - genV P A C) =
      Ring.inverse (1 - qgtPlus P A C) * conePlus P X *
        Ring.inverse (1 - qgtMinus P A C) := by
  rw [ringInverse_one_sub_genV_mul_conePlus hP A C X hunit, mul_assoc,
    conePlus_mul_ringInverse_one_sub_genV hP A C X hunit, ← mul_assoc]

/-- The lower variation has the reversed pair of sheet resolvents. -/
theorem ringInverse_genV_sandwich_coneMinus {P : B} (hP : P * P = P) (A C X : B)
    (hunit : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) * coneMinus P X * Ring.inverse (1 - genV P A C) =
      Ring.inverse (1 - qgtMinus P A C) * coneMinus P X *
        Ring.inverse (1 - qgtPlus P A C) := by
  rw [ringInverse_one_sub_genV_mul_coneMinus hP A C X hunit, mul_assoc,
    coneMinus_mul_ringInverse_one_sub_genV hP A C X hunit, ← mul_assoc]

end InfoGeometry.OperatorAlgebra.PeirceSpine
