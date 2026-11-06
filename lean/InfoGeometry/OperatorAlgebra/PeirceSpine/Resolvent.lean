/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.ResolventTransform
import Mathlib.Algebra.Group.Commute.Units

/-!
# Ordered Peirce charts and their resolvent domain

The two affine charts in this file are both based at `P`. Their signs therefore
differ from the complementary charts named `projChartPlus` and `projChartMinus`.
The existing unipotent conjugations make the order of dressing explicit.

The even element `V = N₊ * N₋ + N₋ * N₊` has two orthogonal diagonal corner
products. The unit domain of `1 - V` agrees with that of either corner
resolvent. On every upper or lower Peirce direction, its inverse sandwich is
the corresponding ordered pair of corner resolvents. All inverse identities
retain an explicit unit-domain hypothesis.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)

include hP

/-- The two same-base affine charts have an odd term in their commutator. -/
theorem same_base_chart_commutator (A C : B) :
    comm (P + conePlus P A) (P + coneMinus P C) =
      genSig P A C - genPhi P A C := by
  peirce_nf hP

/-- Commuting same-base charts force both directed displacements to vanish.
The corner compressions prove this in every characteristic. -/
theorem same_base_chart_commutator_eq_zero_iff (A C : B) :
    comm (P + conePlus P A) (P + coneMinus P C) = 0 ↔
      conePlus P A = 0 ∧ coneMinus P C = 0 := by
  constructor
  · intro h
    have hp : -conePlus P A = 0 := by
      calc
        -conePlus P A =
            P * comm (P + conePlus P A) (P + coneMinus P C) * (1 - P) := by
          peirce_nf hP
        _ = 0 := by rw [h, mul_zero, zero_mul]
    have hm : -coneMinus P C = 0 := by
      calc
        -coneMinus P C =
            (1 - P) * comm (P + conePlus P A) (P + coneMinus P C) * P := by
          peirce_nf hP
        _ = 0 := by rw [h, mul_zero, zero_mul]
    exact ⟨neg_eq_zero.mp hp, neg_eq_zero.mp hm⟩
  · rintro ⟨hp, hm⟩
    simp only [hp, hm, add_zero, comm, sub_self]

/-- Dressing the lower chart by the inverse upper shear gives the corrected
normal form, whose cubic term ends in the upper corner. -/
theorem conjPlusInv_lower_chart_eq (A C : B) :
    conjPlusInv P A (P + coneMinus P C) =
      P + genPhi P A C - genSig P A C - genV P A C * conePlus P A := by
  unfold conjPlusInv
  peirce_nf hP

/-- The dressed chart is an actual idempotent. -/
theorem conjPlusInv_lower_chart_idempotent (A C : B) :
    conjPlusInv P A (P + coneMinus P C) *
        conjPlusInv P A (P + coneMinus P C) =
      conjPlusInv P A (P + coneMinus P C) := by
  unfold conjPlusInv
  peirce_nf hP

/-- Reversing the upper shear changes the linear and commutator terms. -/
theorem conjPlus_lower_chart_eq (A C : B) :
    conjPlus P A (P + coneMinus P C) =
      P - genJ P A C + genSig P A C - genV P A C * conePlus P A := by
  unfold conjPlus
  peirce_nf hP

/-- The two diagonal corner factors multiply to the full even resolvent. -/
theorem one_sub_genV_factorization (A C : B) :
    (1 - conePlus P A * coneMinus P C) *
        (1 - coneMinus P C * conePlus P A) =
      1 - genV P A C := by
  peirce_nf hP

/-- The reverse product has the same value because the two diagonal corner
products annihilate each other. -/
theorem one_sub_genV_factorization_rev (A C : B) :
    (1 - coneMinus P C * conePlus P A) *
        (1 - conePlus P A * coneMinus P C) =
      1 - genV P A C := by
  peirce_nf hP

/-- Invertibility of the full even resolvent is equivalent to invertibility
of the upper corner resolvent. Jacobson's identity supplies the other factor. -/
theorem isUnit_one_sub_genV_iff (A C : B) :
    IsUnit (1 - genV P A C) ↔
      IsUnit (1 - conePlus P A * coneMinus P C) := by
  have hc : Commute (1 - conePlus P A * coneMinus P C)
      (1 - coneMinus P C * conePlus P A) := by
    change (1 - conePlus P A * coneMinus P C) *
          (1 - coneMinus P C * conePlus P A) =
        (1 - coneMinus P C * conePlus P A) *
          (1 - conePlus P A * coneMinus P C)
    rw [one_sub_genV_factorization hP, one_sub_genV_factorization_rev hP]
  rw [← one_sub_genV_factorization hP A C, hc.isUnit_mul_iff]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, (ResolventTransform.isUnit_one_sub_mul_iff
      (conePlus P A) (coneMinus P C)).mp h⟩

/-- Every upper direction sees only the upper factor on its left. -/
theorem inverse_one_sub_genV_mul_conePlus (A C H : B)
    (hV : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) * conePlus P H =
      Ring.inverse (1 - conePlus P A * coneMinus P C) * conePlus P H := by
  have hp := (isUnit_one_sub_genV_iff hP A C).mp hV
  have hm := (ResolventTransform.isUnit_one_sub_mul_iff
    (conePlus P A) (coneMinus P C)).mp hp
  have hfix : Ring.inverse (1 - coneMinus P C * conePlus P A) *
      conePlus P H = conePlus P H := by
    apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hm).2
    peirce_nf hP
  rw [← one_sub_genV_factorization_rev hP A C,
    Ring.inverse_mul (Or.inl hm), mul_assoc, hfix]

/-- Every upper direction sees only the lower factor on its right. -/
theorem conePlus_mul_inverse_one_sub_genV (A C H : B)
    (hV : IsUnit (1 - genV P A C)) :
    conePlus P H * Ring.inverse (1 - genV P A C) =
      conePlus P H * Ring.inverse (1 - coneMinus P C * conePlus P A) := by
  have hp := (isUnit_one_sub_genV_iff hP A C).mp hV
  have hm := (ResolventTransform.isUnit_one_sub_mul_iff
    (conePlus P A) (coneMinus P C)).mp hp
  have hfix : conePlus P H *
      Ring.inverse (1 - conePlus P A * coneMinus P C) = conePlus P H := by
    symm
    apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ hp).2
    peirce_nf hP
  rw [← one_sub_genV_factorization_rev hP A C,
    Ring.inverse_mul (Or.inl hm), ← mul_assoc, hfix]

/-- The two corner resolvents give the full even inverse sandwich on every
upper Peirce direction, including directions distinct from the base point. -/
theorem inverse_one_sub_genV_conePlus_sandwich (A C H : B)
    (hV : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) * conePlus P H *
        Ring.inverse (1 - genV P A C) =
      Ring.inverse (1 - conePlus P A * coneMinus P C) * conePlus P H *
        Ring.inverse (1 - coneMinus P C * conePlus P A) := by
  rw [inverse_one_sub_genV_mul_conePlus hP A C H hV, mul_assoc,
    conePlus_mul_inverse_one_sub_genV hP A C H hV, ← mul_assoc]

/-- Every lower direction sees only the lower factor on its left. -/
theorem inverse_one_sub_genV_mul_coneMinus (A C H : B)
    (hV : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) * coneMinus P H =
      Ring.inverse (1 - coneMinus P C * conePlus P A) * coneMinus P H := by
  have hp := (isUnit_one_sub_genV_iff hP A C).mp hV
  have hfix : Ring.inverse (1 - conePlus P A * coneMinus P C) *
      coneMinus P H = coneMinus P H := by
    apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hp).2
    peirce_nf hP
  rw [← one_sub_genV_factorization hP A C,
    Ring.inverse_mul (Or.inl hp), mul_assoc, hfix]

/-- Every lower direction sees only the upper factor on its right. -/
theorem coneMinus_mul_inverse_one_sub_genV (A C H : B)
    (hV : IsUnit (1 - genV P A C)) :
    coneMinus P H * Ring.inverse (1 - genV P A C) =
      coneMinus P H * Ring.inverse (1 - conePlus P A * coneMinus P C) := by
  have hp := (isUnit_one_sub_genV_iff hP A C).mp hV
  have hm := (ResolventTransform.isUnit_one_sub_mul_iff
    (conePlus P A) (coneMinus P C)).mp hp
  have hfix : coneMinus P H *
      Ring.inverse (1 - coneMinus P C * conePlus P A) = coneMinus P H := by
    symm
    apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ hm).2
    peirce_nf hP
  rw [← one_sub_genV_factorization hP A C,
    Ring.inverse_mul (Or.inl hp), ← mul_assoc, hfix]

/-- The lower-direction sandwich uses the opposite ordered pair of factors. -/
theorem inverse_one_sub_genV_coneMinus_sandwich (A C H : B)
    (hV : IsUnit (1 - genV P A C)) :
    Ring.inverse (1 - genV P A C) * coneMinus P H *
        Ring.inverse (1 - genV P A C) =
      Ring.inverse (1 - coneMinus P C * conePlus P A) * coneMinus P H *
        Ring.inverse (1 - conePlus P A * coneMinus P C) := by
  rw [inverse_one_sub_genV_mul_coneMinus hP A C H hV, mul_assoc,
    coneMinus_mul_inverse_one_sub_genV hP A C H hV, ← mul_assoc]

end InfoGeometry.OperatorAlgebra.PeirceSpine
