/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.FreudenthalSymplecticContactLieAlgebra

/-!
# Normalization forced by the mixed contact Jacobi component

Contract: perturb two coefficients in the existing actual five-graded contact
bracket, keeping its rank-two operator and extreme-grade actions unchanged.
Compute its `(-1,-1,+1)` Leibniz defect on arbitrary full Freudenthal charges.
Fixing either existing coefficient forces the other. No simultaneous uniqueness
claim is made: on a two-dimensional charge space the two defects are dependent.
No exceptional Lie algebra identification or extra cubic law is used.

Search/reuse: the contact bracket, faithful representation, and Lie structure
are owned by FreudenthalSymplecticContactRepresentation/ContactLieAlgebra.
TKKJacobiObstruction proves the uncorrected defect and its isotropic-set criterion.
No coefficient-normalization converse was found in the searched Exceptional
and Lie owners. The existing alphaCharge/betaCharge only witness necessity;
the identities concern all charges, with their full Jordan-valued components.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- Modify only the mixed grading-scalar and negative Heisenberg coefficients. -/
def contactBracketWithCoefficients (c d : ℝ)
    (u v : FiveGradedCarrier D) : FiveGradedCarrier D :=
  { symplecticContactBracket D u v with
    minus2 := (-2 * u.zero_scale * v.minus2 + 2 * v.zero_scale * u.minus2) +
      d * FreudenthalCharge.symplecticForm D u.minus1 v.minus1
    zero_scale := (u.plus2 * v.minus2 - v.plus2 * u.minus2) +
      c * (FreudenthalCharge.symplecticForm D u.minus1 v.plus1 -
        FreudenthalCharge.symplecticForm D v.minus1 u.plus1) }

theorem contactBracketWithCoefficients_standard (u v : FiveGradedCarrier D) :
    contactBracketWithCoefficients D 1 (-2) u v = symplecticContactBracket D u v := by
  apply FiveGradedCarrier.ext <;>
    simp [contactBracketWithCoefficients, symplecticContactBracket] <;> ring

/-- Actual minus-one component of the parameterized operator bracket's Leibniz defect. -/
def contactMixedJacobiMinus (c d : ℝ) (x y z : FreudenthalCharge J) :
    FreudenthalCharge J :=
  (contactBracketWithCoefficients D c d (injChargeMinus D x)
    (contactBracketWithCoefficients D c d (injChargeMinus D y) (injChargePlus D z))).minus1 -
  (contactBracketWithCoefficients D c d
    (contactBracketWithCoefficients D c d (injChargeMinus D x) (injChargeMinus D y))
    (injChargePlus D z)).minus1 -
  (contactBracketWithCoefficients D c d (injChargeMinus D y)
    (contactBracketWithCoefficients D c d (injChargeMinus D x) (injChargePlus D z))).minus1

theorem contactMixedJacobiMinus_eq (c d : ℝ) (x y z : FreudenthalCharge J) :
    contactMixedJacobiMinus D c d x y z =
      (1 - c) • (FreudenthalCharge.symplecticForm D z y • x +
        FreudenthalCharge.symplecticForm D x z • y) +
      (2 + d) • (FreudenthalCharge.symplecticForm D x y • z) := by
  simp [contactMixedJacobiMinus, contactBracketWithCoefficients,
    symplecticContactBracket, injChargeMinus, injChargePlus,
    mixedSymplecticBracket_val, symplecticRankTwo_apply]
  rw [FreudenthalCharge.symplectic_form_skew D y x,
    FreudenthalCharge.symplectic_form_skew D y z,
    FreudenthalCharge.symplectic_form_skew D z x]
  module

/-- With the native negative Heisenberg coefficient, Jacobi forces scalar coefficient one. -/
theorem contactMixedJacobiMinus_fixed_heisenberg_iff (c : ℝ) :
    (∀ x y z : FreudenthalCharge J, contactMixedJacobiMinus D c (-2) x y z = 0) ↔
      c = 1 := by
  constructor
  · intro h
    have hw := h (alphaCharge (J := J)) (betaCharge (J := J)) (alphaCharge (J := J))
    rw [contactMixedJacobiMinus_eq] at hw
    have ha := congrArg (fun q : FreudenthalCharge J => q.alpha) hw
    simp [alphaCharge, betaCharge, FreudenthalCharge.symplecticForm] at ha
    linarith
  · rintro rfl x y z
    rw [contactMixedJacobiMinus_eq]
    norm_num

/-- With the native mixed scalar coefficient, Jacobi forces Heisenberg coefficient minus two. -/
theorem contactMixedJacobiMinus_fixed_scalar_iff (d : ℝ) :
    (∀ x y z : FreudenthalCharge J, contactMixedJacobiMinus D 1 d x y z = 0) ↔
      d = -2 := by
  constructor
  · intro h
    have hw := h (alphaCharge (J := J)) (betaCharge (J := J)) (alphaCharge (J := J))
    rw [contactMixedJacobiMinus_eq] at hw
    have ha := congrArg (fun q : FreudenthalCharge J => q.alpha) hw
    simp [alphaCharge, betaCharge, FreudenthalCharge.symplecticForm] at ha
    linarith
  · rintro rfl x y z
    rw [contactMixedJacobiMinus_eq]
    norm_num

end InfoGeometry.Exceptional.Freudenthal
