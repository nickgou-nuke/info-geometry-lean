/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.WittenSpinorHelicity
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The Parke--Taylor rational expression and its native spinor weights

This owner defines Witten's equation (2.14) as a rational expression on the
nonvanishing adjacent-bracket locus and proves its cyclic covariance and
little-group weights. There is no definition of a Yang--Mills scattering
amplitude here and no assumed equality with one. The domain includes `3 ≤ n`
so that an empty product is not mistaken for physical external data.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Twistor.WittenParkeTaylor

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.WittenSpinorHelicity

variable {n : ℕ}

/-- The cyclic product uses Mathlib's actual permutation of the finite labels. -/
def cyclicSpinorDenominator (lambda : Fin n → Spinor2) : ℂ :=
  ∏ i, spinorBracket (lambda i) (lambda (finRotate n i))

/-- The ordinary rational chart has at least three legs and no adjacent pole. -/
def IsParkeTaylorRegular (lambda : Fin n → Spinor2) : Prop :=
  3 ≤ n ∧ ∀ i, spinorBracket (lambda i) (lambda (finRotate n i)) ≠ 0

theorem cyclicSpinorDenominator_ne_zero
    (lambda : Fin n → Spinor2) (hlambda : IsParkeTaylorRegular lambda) :
    cyclicSpinorDenominator lambda ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hlambda.2 i)

/-- The color-ordered rational expression; delta functions and the color trace
are absent, as in Witten's reduced formula. -/
def parkeTaylorExpression (g : ℂ) (lambda : Fin n → Spinor2) (r s : Fin n) : ℂ :=
  g ^ (n - 2) * spinorBracket (lambda r) (lambda s) ^ 4 /
    cyclicSpinorDenominator lambda

theorem cyclicSpinorDenominator_rotate (lambda : Fin n → Spinor2) :
    cyclicSpinorDenominator (fun i => lambda (finRotate n i)) =
      cyclicSpinorDenominator lambda := by
  exact Fintype.prod_equiv (finRotate n) _ _ (fun _ => rfl)

theorem isParkeTaylorRegular_rotate
    (lambda : Fin n → Spinor2) (hlambda : IsParkeTaylorRegular lambda) :
    IsParkeTaylorRegular (fun i => lambda (finRotate n i)) := by
  exact ⟨hlambda.1, fun i => hlambda.2 (finRotate n i)⟩

/-- Cyclic relabelling transports both negative-helicity labels as well. -/
theorem parkeTaylorExpression_rotate
    (g : ℂ) (lambda : Fin n → Spinor2) (r s : Fin n) :
    parkeTaylorExpression g (fun i => lambda (finRotate n i))
      ((finRotate n).symm r) ((finRotate n).symm s) =
      parkeTaylorExpression g lambda r s := by
  simp only [parkeTaylorExpression, Equiv.apply_symm_apply,
    cyclicSpinorDenominator_rotate]

theorem cyclicSpinorDenominator_scale
    (c : Fin n → ℂ) (lambda : Fin n → Spinor2) :
    cyclicSpinorDenominator (fun i => c i • lambda i) =
      (∏ i, c i) ^ 2 * cyclicSpinorDenominator lambda := by
  unfold cyclicSpinorDenominator
  simp only [spinorBracket_smul]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hrotate : (∏ i, c (finRotate n i)) = ∏ i, c i :=
    Fintype.prod_equiv (finRotate n) _ _ (fun _ => rfl)
  rw [hrotate, pow_two]

/-- Nonzero little-group scalars preserve the actual rational domain. -/
theorem isParkeTaylorRegular_scale
    (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (lambda : Fin n → Spinor2) (hlambda : IsParkeTaylorRegular lambda) :
    IsParkeTaylorRegular (fun i => c i • lambda i) := by
  refine ⟨hlambda.1, fun i => ?_⟩
  rw [spinorBracket_smul]
  exact mul_ne_zero (mul_ne_zero (hc i) (hc (finRotate n i))) (hlambda.2 i)

/-- Each denominator leg occurs twice, while the two distinguished numerator
legs occur four times. This proves the full independent-scaling formula. -/
theorem parkeTaylorExpression_littleGroup
    (g : ℂ) (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (lambda : Fin n → Spinor2) (hlambda : IsParkeTaylorRegular lambda)
    (r s : Fin n) :
    parkeTaylorExpression g (fun i => c i • lambda i) r s =
      ((c r * c s) ^ 4 / (∏ i, c i) ^ 2) *
        parkeTaylorExpression g lambda r s := by
  have hden := cyclicSpinorDenominator_ne_zero lambda hlambda
  have hcprod : (∏ i, c i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hc i)
  rw [parkeTaylorExpression, cyclicSpinorDenominator_scale, spinorBracket_smul,
    parkeTaylorExpression]
  field_simp [hden, hcprod] <;> ring

/-- Rescale one particle's spinor, retaining the remaining native spinors. -/
def scaleOneSpinor (k : Fin n) (c : ℂ) (lambda : Fin n → Spinor2) :
    Fin n → Spinor2 :=
  fun i => (if i = k then c else 1) • lambda i

/-- A leg outside the two distinguished labels has little-group weight -2. -/
theorem parkeTaylorExpression_positive_leg_weight
    (g c : ℂ) (hc : c ≠ 0) (lambda : Fin n → Spinor2)
    (hlambda : IsParkeTaylorRegular lambda) (r s k : Fin n)
    (hkr : k ≠ r) (hks : k ≠ s) :
    parkeTaylorExpression g (scaleOneSpinor k c lambda) r s =
      c⁻¹ ^ 2 * parkeTaylorExpression g lambda r s := by
  have hscale := parkeTaylorExpression_littleGroup g
    (fun i => if i = k then c else 1)
    (by intro i; split_ifs <;> simp_all)
    lambda hlambda r s
  change parkeTaylorExpression g
    (fun i => (if i = k then c else 1) • lambda i) r s = _
  rw [hscale]
  simp [Ne.symm hkr, Ne.symm hks, inv_pow]

/-- Either distinguished leg has little-group weight +2 when the labels differ. -/
theorem parkeTaylorExpression_negative_leg_weight
    (g c : ℂ) (hc : c ≠ 0) (lambda : Fin n → Spinor2)
    (hlambda : IsParkeTaylorRegular lambda) (r s : Fin n) (hrs : r ≠ s) :
    parkeTaylorExpression g (scaleOneSpinor r c lambda) r s =
      c ^ 2 * parkeTaylorExpression g lambda r s := by
  have hscale := parkeTaylorExpression_littleGroup g
    (fun i => if i = r then c else 1)
    (by intro i; split_ifs <;> simp_all)
    lambda hlambda r s
  have hweight : c ^ 4 / c ^ 2 = c ^ 2 := by
    field_simp [hc]
    <;> ring
  change parkeTaylorExpression g
    (fun i => (if i = r then c else 1) • lambda i) r s = _
  rw [hscale]
  simp [Ne.symm hrs, hweight]

/-- A concrete regular four-leg spinor configuration. No momentum-conservation
or reality assumption is inferred from this algebraic domain witness. -/
def fourPointSpinors : Fin 4 → Spinor2 := fun i => ![1, (i.val : ℂ)]

theorem fourPointSpinors_regular : IsParkeTaylorRegular fourPointSpinors := by
  constructor
  · norm_num
  · intro i
    fin_cases i <;>
      norm_num [fourPointSpinors, spinorBracket_apply, finRotate_apply]

/-- The expression has a nonzero value on its genuine rational domain. -/
theorem fourPoint_parkeTaylor_value :
    parkeTaylorExpression 1 fourPointSpinors 0 1 = -(1 / 3 : ℂ) := by
  norm_num [parkeTaylorExpression, cyclicSpinorDenominator, fourPointSpinors,
    spinorBracket_apply, Fin.prod_univ_four, finRotate_apply]

end InfoGeometry.Twistor.WittenParkeTaylor
