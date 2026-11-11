/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorConstituentKinematics
import InfoGeometry.Twistor.PerjesMomentOperator
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Distinct Gram and mass invariants of an actual twistor pair

The Witt Gram determinant is the induced alternating-tensor contraction.
The paper-normalized mass is instead twice the existing lower-spinor mass
squared. An explicit family independently realizes both complex pairings,
even when both constituents have zero Witt self-pairing.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwoTwistorGramMass

open PenroseIncidence PerjesConventions TwistorKinematicTensor
open TwistorConstituentKinematics InfinityTwistor TwoTwistorPlucker
open PerjesMomentOperator
open scoped Matrix BigOperators

/-- Two ordered constituents, without rank or nonzero assumptions. -/
abbrev PairFrame := Packet (Fin 2)

/-- Conjugate-first Witt Gram matrix on the actual constituent labels. -/
def gram (Z : PairFrame) : ComplexSpacetime := fun i j => wittPair (Z i) (Z j)

theorem gram_hermitian (Z : PairFrame) : (gram Z)ᴴ = gram Z := by
  ext i j
  exact wittPair_conj (Z j) (Z i)

/-- The factor two is a convention conversion, not a redefinition of `pairMassSq`. -/
def paperMassSq (Z : PairFrame) : ℝ := 2 * pairMassSq (Z 0) (Z 1)

theorem paperMassSq_eq_infinity_normSq (Z : PairFrame) :
    paperMassSq Z = 2 * Complex.normSq (infinityTwistor (Z 0) (Z 1)) := rfl

theorem paperMassSq_nonneg (Z : PairFrame) : 0 ≤ paperMassSq Z :=
  mul_nonneg (by norm_num) (pairMassSq_nonneg _ _)

theorem paperMassSq_eq_twice_momentum_det (Z : PairFrame) :
    (paperMassSq Z : ℂ) = 2 * (momentum (Z 0) + momentum (Z 1)).det := by
  rw [pairMomentum_determinant]
  simp [paperMassSq]

/-- The full ordered alternating two-tensor, on the owner's upper/lower slots. -/
def bivector (Z : PairFrame) : KinematicMatrix :=
  fun a b => component (Z 0) a * component (Z 1) b -
    component (Z 1) a * component (Z 0) b

theorem bivector_transpose (Z : PairFrame) : (bivector Z)ᵀ = -bivector Z := by
  ext a b
  simp [bivector, Matrix.transpose_apply]
  ring

/-- The momentum-sector component is the existing Plücker coordinate. -/
theorem bivector_lower_minor (Z : PairFrame) :
    bivector Z (.inr 0) (.inr 1) = (twistorPairPlucker (Z 0) (Z 1)).p23 := by
  simp [bivector, component, twistorPairPlucker, twistorProjectiveVector,
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine]
  ring

/-- Full Einstein contraction, with no factor of one half built into the definition. -/
def bivectorContraction (Z : PairFrame) : ℂ :=
  ∑ a, ∑ b, bivector Z a b *
    (conjugateCoordinate (Z 0) a * conjugateCoordinate (Z 1) b -
      conjugateCoordinate (Z 1) a * conjugateCoordinate (Z 0) b)

theorem bivectorContraction_eq_twice_gram_det (Z : PairFrame) :
    bivectorContraction Z = 2 * (gram Z).det := by
  simp [bivectorContraction, bivector, conjugateCoordinate, component, gram,
    wittPair, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem half_bivectorContraction_eq_gram_det (Z : PairFrame) :
    bivectorContraction Z / 2 = (gram Z).det := by
  rw [bivectorContraction_eq_twice_gram_det]
  ring

/-- Gram determinant in self-pairing/cross-pairing coordinates. -/
theorem gram_det (Z : PairFrame) :
    (gram Z).det = wittPair (Z 0) (Z 0) * wittPair (Z 1) (Z 1) -
      (Complex.normSq (wittPair (Z 0) (Z 1)) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [gram, Complex.normSq_eq_conj_mul_self]
  rw [show (starRingEnd ℂ) (wittPair (Z 0) (Z 1)) = wittPair (Z 1) (Z 0) from
    wittPair_conj (Z 0) (Z 1)]
  ring

/-- In the null-self-pairing regime the conformal contraction has a negative sign. -/
theorem gram_det_of_null (Z : PairFrame)
    (h0 : wittPair (Z 0) (Z 0) = 0) (h1 : wittPair (Z 1) (Z 1) = 0) :
    (gram Z).det = -(Complex.normSq (wittPair (Z 0) (Z 1)) : ℂ) := by
  rw [gram_det, h0, h1]
  simp

/-- Exact difference of the paper mass square and the real conformal determinant. -/
def massConformalDefect (Z : PairFrame) : ℝ := paperMassSq Z - (gram Z).det.re

theorem massConformalDefect_of_null (Z : PairFrame)
    (h0 : wittPair (Z 0) (Z 0) = 0) (h1 : wittPair (Z 1) (Z 1) = 0) :
    massConformalDefect Z =
      2 * Complex.normSq (infinityTwistor (Z 0) (Z 1)) +
        Complex.normSq (wittPair (Z 0) (Z 1)) := by
  simp [massConformalDefect, paperMassSq_eq_infinity_normSq,
    gram_det_of_null Z h0 h1]

/-- Strict positivity needs a genuine nonzero pairing, not only null self-pairings. -/
theorem massConformalDefect_pos_of_null (Z : PairFrame)
    (h0 : wittPair (Z 0) (Z 0) = 0) (h1 : wittPair (Z 1) (Z 1) = 0)
    (hn : infinityTwistor (Z 0) (Z 1) ≠ 0 ∨ wittPair (Z 0) (Z 1) ≠ 0) :
    0 < massConformalDefect Z := by
  rw [massConformalDefect_of_null Z h0 h1]
  rcases hn with hm | ht
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num) (Complex.normSq_pos.mpr hm)) (Complex.normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) (Complex.normSq_pos.mpr ht)

/-- Ordered composition of the existing mixed-index moment operators. -/
theorem momentOperator_mul (Z W : Twistor4) :
    momentOperator Z * momentOperator W =
      wittPair Z W • Matrix.vecMulVec (component Z) (conjugateCoordinate W) := by
  ext a b
  simp [momentOperator, Matrix.vecMulVec, Matrix.mul_apply, conjugateCoordinate,
    component, wittPair, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem trace_momentOperator (Z : Twistor4) :
    Matrix.trace (momentOperator Z) = wittPair Z Z := by
  simp [momentOperator, Matrix.trace, Matrix.vecMulVec, conjugateCoordinate,
    component, wittPair, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

/-- The round-trip trace is the cross-pairing norm, although the operators need not commute. -/
theorem trace_momentOperator_mul (Z W : Twistor4) :
    Matrix.trace (momentOperator Z * momentOperator W) =
      (Complex.normSq (wittPair Z W) : ℂ) := by
  rw [momentOperator_mul]
  simp [Matrix.trace, Matrix.vecMulVec, conjugateCoordinate, component,
    wittPair, Fintype.sum_sum_type, Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self]
  ring

/-- The Gram determinant is a difference of operator self and round-trip readouts. -/
theorem gram_det_eq_operator_readouts (Z : PairFrame) :
    (gram Z).det = Matrix.trace (momentOperator (Z 0)) *
        Matrix.trace (momentOperator (Z 1)) -
      Matrix.trace (momentOperator (Z 0) * momentOperator (Z 1)) := by
  rw [gram_det, trace_momentOperator, trace_momentOperator, trace_momentOperator_mul]

/-- Exact idempotence defect of the actual noncommutative moment operator. -/
theorem momentOperator_idempotence_defect (Z : Twistor4) :
    momentOperator Z * momentOperator Z - momentOperator Z =
      (wittPair Z Z - 1) • momentOperator Z := by
  rw [momentOperator_square, sub_smul, one_smul]

/-- All positive powers of the actual moment endomorphism, not merely its trace. -/
theorem momentOperator_pow_succ (Z : Twistor4) (n : ℕ) :
    momentOperator Z ^ (n + 1) = wittPair Z Z ^ n • momentOperator Z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Matrix.smul_mul, momentOperator_square, smul_smul, pow_succ]

/-- Independent complex parameters on two Witt-isotropic vectors. -/
def independentFrame (r t : ℂ) : PairFrame :=
  ![((0 : Spinor2), ![1, 0]), ((![t, 0] : Spinor2), ![0, r])]

@[simp] theorem independentFrame_infinity (r t : ℂ) :
    infinityTwistor (independentFrame r t 0) (independentFrame r t 1) = r := by
  simp [independentFrame, infinityTwistor]

@[simp] theorem independentFrame_cross (r t : ℂ) :
    wittPair (independentFrame r t 0) (independentFrame r t 1) = t := by
  simp [independentFrame, wittPair, Fin.sum_univ_two]

@[simp] theorem independentFrame_self (r t : ℂ) (i : Fin 2) :
    wittPair (independentFrame r t i) (independentFrame r t i) = 0 := by
  fin_cases i <;> simp [independentFrame, wittPair, Fin.sum_univ_two]

@[simp] theorem independentFrame_mass (r t : ℂ) :
    paperMassSq (independentFrame r t) = 2 * Complex.normSq r := by
  rw [paperMassSq_eq_infinity_normSq, independentFrame_infinity]

/-- Joint surjectivity of the two complex pairings; no identification of them is possible. -/
theorem pairings_surjective :
    Function.Surjective (fun Z : PairFrame =>
      (infinityTwistor (Z 0) (Z 1), wittPair (Z 0) (Z 1))) := by
  rintro ⟨r, t⟩
  exact ⟨independentFrame r t,
    Prod.ext (independentFrame_infinity r t) (independentFrame_cross r t)⟩

/-- Every pair of nonnegative squared values occurs, with null self-pairings. -/
theorem squared_invariants_realize (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ Z : PairFrame, paperMassSq Z = a ∧
      Complex.normSq (wittPair (Z 0) (Z 1)) = b ∧
      ∀ i, wittPair (Z i) (Z i) = 0 := by
  refine ⟨independentFrame (Real.sqrt (a / 2)) (Real.sqrt b), ?_, ?_, ?_⟩
  · rw [independentFrame_mass]
    simp only [Complex.normSq_ofReal]
    nlinarith [Real.sq_sqrt (div_nonneg ha (by norm_num : (0 : ℝ) ≤ 2))]
  · rw [independentFrame_cross]
    simpa only [Complex.normSq_ofReal, pow_two] using Real.sq_sqrt hb
  · exact independentFrame_self _ _

/-- A positive mass at zero conformal Gram matrix. -/
theorem positive_mass_zero_gram :
    paperMassSq (independentFrame 1 0) = 2 ∧ gram (independentFrame 1 0) = 0 := by
  constructor
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, independentFrame, wittPair, Fin.sum_univ_two]

/-- Both twistors are null, have parallel nonzero momenta, and have nonzero cross-pairing. -/
theorem massless_null_crossed_witness :
    let Z : PairFrame :=
      ![((0 : Spinor2), ![1, 0]), ((![Complex.I, 0] : Spinor2), ![1, 0])]
    paperMassSq Z = 0 ∧ wittPair (Z 0) (Z 1) = Complex.I ∧
      (∀ i, wittPair (Z i) (Z i) = 0) := by
  intro Z
  refine ⟨?_, ?_, ?_⟩
  · simp [paperMassSq, pairMassSq, spinorMinor, Z]
  · simp [wittPair, Z, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> simp [wittPair, Z, Fin.sum_univ_two]

end InfoGeometry.Twistor.TwoTwistorGramMass
