/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.FreudenthalSymplecticTKKTotalBracket
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The mixed Jacobi obstruction for the symplectic TKK bracket

The existing symplectic socket supplies the zero-grade action and bracket
laws, but not the extra triple identity needed for the full TKK Jacobi law.
This file computes the `(-1,+1,-1)` defect and characterizes its universal
vanishing on a set by pairwise symplectic orthogonality.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem tkk_mixed_jacobi_plus1_component
    (x z : FreudenthalCharge J) (y : FreudenthalCharge J) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).minus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).minus1 =
      (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x -
        (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z := by
  simp [tkkTotalBracket, injMinus1, injPlus1]
  module

/-- The mixed Jacobi component vanishes for every triple in a set exactly
when the set is pairwise symplectically orthogonal. This characterizes the
actual total-bracket obstruction without assuming the desired triple law. -/
theorem tkk_mixed_jacobi_on_iff_pairing_zero
    (s : Set (FreudenthalCharge J)) :
    (∀ x ∈ s, ∀ z ∈ s, ∀ y ∈ s,
      (tkkTotalBracket D (injMinus1 D x)
        (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).minus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).minus1 = 0) ↔
    (∀ x ∈ s, ∀ z ∈ s, FreudenthalCharge.symplecticForm D x z = 0) := by
  constructor
  · intro h x hx z hz
    have hrepeated := h x hx z hz x hx
    rw [tkk_mixed_jacobi_plus1_component, sub_eq_zero] at hrepeated
    simp only [mixedSymplecticBracket_val] at hrepeated
    exact (symplecticRankTwo_repeated_mixed_iff D x z).mp hrepeated
  · intro h x hx z hz y hy
    rw [tkk_mixed_jacobi_plus1_component]
    simp only [mixedSymplecticBracket_val, symplecticRankTwo_apply,
      h y hy x hx, h z hz x hx, h y hy z hz, h x hx z hz,
      zero_smul, add_zero, sub_self]

theorem tkk_mixed_jacobi_minus1_of_triple_identity
    (x z : FreudenthalCharge J) (y : FreudenthalCharge J)
    (htriple :
      (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x =
        (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).minus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).minus1 = 0 := by
  rw [tkk_mixed_jacobi_plus1_component D x z y, htriple]
  exact sub_self _

theorem tkk_mixed_jacobi_symmetric_component
    (x z : FreudenthalCharge J) (y : FreudenthalCharge J) :
    (tkkTotalBracket D (injPlus1 D x)
      (tkkTotalBracket D (injMinus1 D y) (injPlus1 D z))).plus1 +
      (tkkTotalBracket D (injMinus1 D y)
        (tkkTotalBracket D (injPlus1 D z) (injPlus1 D x))).plus1 +
      (tkkTotalBracket D (injPlus1 D z)
        (tkkTotalBracket D (injPlus1 D x) (injMinus1 D y))).plus1 =
      (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z -
        (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x := by
  simp [tkkTotalBracket, injMinus1, injPlus1]
  module

theorem tkk_mixed_jacobi_plus1_of_triple_identity
    (x z : FreudenthalCharge J) (y : FreudenthalCharge J)
    (htriple :
      (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z =
        (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x) :
    (tkkTotalBracket D (injPlus1 D x)
      (tkkTotalBracket D (injMinus1 D y) (injPlus1 D z))).plus1 +
      (tkkTotalBracket D (injMinus1 D y)
        (tkkTotalBracket D (injPlus1 D z) (injPlus1 D x))).plus1 +
      (tkkTotalBracket D (injPlus1 D z)
        (tkkTotalBracket D (injPlus1 D x) (injMinus1 D y))).plus1 = 0 := by
  rw [tkk_mixed_jacobi_symmetric_component D x z y, htriple]
  exact sub_self _

theorem tkk_mixed_jacobi_minus1_obstruction_explicit
    (x z : FreudenthalCharge J) (y : FreudenthalCharge J) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).minus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).minus1 =
      FreudenthalCharge.symplecticForm D y x • z +
        FreudenthalCharge.symplecticForm D z x • y -
        (FreudenthalCharge.symplecticForm D y z • x +
          FreudenthalCharge.symplecticForm D x z • y) := by
  rw [tkk_mixed_jacobi_plus1_component]
  simp only [mixedSymplecticBracket_val, symplecticRankTwo_apply]

/-! Exact argument-ordered readback of the `(-1,-1,+1)` Jacobiator.  Keeping
the rank-two terms unexpanded here makes the sign convention of the total
bracket explicit. -/
theorem tkk_minus_minus_plus_jacobiator_rankTwo
    (x y z : FreudenthalCharge J) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injMinus1 D y) (injPlus1 D z))).minus1 +
      (tkkTotalBracket D (injMinus1 D y)
        (tkkTotalBracket D (injPlus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injPlus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injMinus1 D y))).minus1 =
      -symplecticRankTwo D y z x + symplecticRankTwo D x z y := by
  simp [tkkTotalBracket, injMinus1, injPlus1, mixedSymplecticBracket_val]

theorem tkk_minus_minus_plus_jacobiator_expanded
    (x y z : FreudenthalCharge J) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injMinus1 D y) (injPlus1 D z))).minus1 +
      (tkkTotalBracket D (injMinus1 D y)
        (tkkTotalBracket D (injPlus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injPlus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injMinus1 D y))).minus1 =
      -(FreudenthalCharge.symplecticForm D z x • y +
        FreudenthalCharge.symplecticForm D y x • z) +
        (FreudenthalCharge.symplecticForm D z y • x +
          FreudenthalCharge.symplecticForm D x y • z) := by
  rw [tkk_minus_minus_plus_jacobiator_rankTwo]
  simp only [symplecticRankTwo_apply]

theorem tkk_minus_minus_plus_jacobiator_jacobiPattern
    (x y z : FreudenthalCharge J) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injMinus1 D y) (injPlus1 D z))).minus1 +
      (tkkTotalBracket D (injMinus1 D y)
        (tkkTotalBracket D (injPlus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injPlus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injMinus1 D y))).minus1 =
      FreudenthalCharge.symplecticForm D x z • y -
        FreudenthalCharge.symplecticForm D y z • x +
          (2 * FreudenthalCharge.symplecticForm D x y) • z := by
  rw [tkk_minus_minus_plus_jacobiator_rankTwo]
  exact symplecticRankTwo_jacobi_pattern D x y z

theorem tkk_mixed_jacobi_minus1_eq_zero_iff
    (x z : FreudenthalCharge J) (y : FreudenthalCharge J) :
    ((tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).minus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).minus1 = 0) ↔
      (FreudenthalCharge.symplecticForm D y x • z +
        FreudenthalCharge.symplecticForm D z x • y -
        (FreudenthalCharge.symplecticForm D y z • x +
          FreudenthalCharge.symplecticForm D x z • y) = 0) := by
  rw [tkk_mixed_jacobi_minus1_obstruction_explicit]

end InfoGeometry.Exceptional.Freudenthal
