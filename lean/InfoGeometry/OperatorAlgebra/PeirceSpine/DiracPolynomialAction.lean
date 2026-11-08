/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingTransfer
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectParity
import InfoGeometry.Core.IdempotentDefectIteration
import Mathlib.Algebra.Star.Basic

/-!
# Peirce Dirac polynomials

This file packages polynomial identities for the Peirce grading and the
two-wave operator. It does not assert analytic spectral-triple axioms or
interpret the resulting ring polynomials as physical actions.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- The algebraic Dirac operator obtained by adding the Peirce grading to the
odd two-wave operator. -/
def peirceMassDirac (P A C : B) : B := invS P + genPhi P A C

/-- The chiral-sign variant of `peirceMassDirac`. -/
def peirceChiralDirac (P A C : B) : B := invS P + genJ P A C

/-- The quartic polynomial `D⁴ - D²`, with multiplication kept ordered. -/
def diracQuarticPolynomial (D : B) : B := (D * D) * (D * D) - D * D

variable {P : B} (hP : P * P = P)
include hP

/-- The grading-plus-wave operator has square `1 + V`. -/
theorem peirce_mass_dirac_square (A C : B) :
    peirceMassDirac P A C * peirceMassDirac P A C = 1 + genV P A C := by
  dsimp [peirceMassDirac]
  peirce_nf hP

/-- The grading-plus-current operator has square `1 - V`. -/
theorem peirce_chiral_dirac_square (A C : B) :
    peirceChiralDirac P A C * peirceChiralDirac P A C = 1 - genV P A C := by
  dsimp [peirceChiralDirac]
  peirce_nf hP

/-- The Peirce grading is an involution. -/
theorem peirce_chirality_involution : invS P * invS P = 1 := by
  peirce_nf hP

/-- The two-wave Yukawa term is odd under the Peirce grading. -/
theorem peirce_yukawa_chirality_odd (A C : B) :
    anticomm (invS P) (genPhi P A C) = 0 := by
  peirce_nf hP

/-- Adding the grading itself to the odd two-wave term changes the even
spectral-triple parity equation by the exact term `2`. -/
theorem peirce_mass_dirac_chirality_parity_defect (A C : B) :
    anticomm (invS P) (peirceMassDirac P A C) =
      (2 : ℤ) • (1 : B) := by
  dsimp [peirceMassDirac]
  peirce_nf hP

/-- Commuting with the cut makes the commutator with the odd two-wave
operator an odd Peirce component. This is the algebraic one-form parity law. -/
theorem peirce_yukawa_commutator_is_odd (A C a : B)
    (hEven : comm P a = 0) :
    anticomm (invS P) (comm (genPhi P A C) a) = 0 := by
  have hPa : P * a = a * P := by
    change P * a - a * P = 0 at hEven
    exact sub_eq_zero.mp hEven
  have hSa : invS P * a = a * invS P := by
    dsimp [invS]
    noncomm_ring [hPa]
  have hOdd : anticomm (invS P) (genPhi P A C) = 0 :=
    peirce_yukawa_chirality_odd hP A C
  change invS P * genPhi P A C + genPhi P A C * invS P = 0 at hOdd
  change invS P * (genPhi P A C * a - a * genPhi P A C) +
    (genPhi P A C * a - a * genPhi P A C) * invS P = 0
  have hFactor :
      invS P * (genPhi P A C * a - a * genPhi P A C) +
          (genPhi P A C * a - a * genPhi P A C) * invS P =
        (invS P * genPhi P A C + genPhi P A C * invS P) * a -
          a * (invS P * genPhi P A C + genPhi P A C * invS P) := by
    have hLeft := congrArg (fun z : B => z * genPhi P A C) hSa
    have hRight := congrArg (fun z : B => genPhi P A C * z) hSa.symm
    calc
      _ = invS P * genPhi P A C * a -
          (invS P * a) * genPhi P A C +
          genPhi P A C * (a * invS P) -
          a * genPhi P A C * invS P := by noncomm_ring
      _ = invS P * genPhi P A C * a -
          (a * invS P) * genPhi P A C +
          genPhi P A C * (invS P * a) -
          a * genPhi P A C * invS P := by rw [hLeft, hRight]
      _ = _ := by noncomm_ring
  rw [hFactor, hOdd]
  noncomm_ring

omit hP in
/-- Every fixed point of the Peirce odd projection has a two-wave
parameterization. Thus arbitrary odd Peirce perturbations are included in the
amplitude-based fluctuation theorems. -/
theorem peirce_odd_grade_representation (X : B)
    (hOdd : oddGrade P X = X) : ∃ A C : B, genPhi P A C = X := by
  exact ⟨X, X, hOdd⟩

/-- Products of two Connes commutator one-forms associated to even
coordinates remain in the diagonal Peirce algebra. The hypotheses explicitly
require both coordinates to commute with the cut. -/
theorem peirce_one_form_product_is_even (A C A' C' a b : B)
    (hEvenA : comm P a = 0) (hEvenB : comm P b = 0) :
    comm P (comm (genPhi P A C) a * comm (genPhi P A' C') b) = 0 := by
  have hPa : P * a = a * P := sub_eq_zero.mp hEvenA
  have hPb : P * b = b * P := sub_eq_zero.mp hEvenB
  have hCompA : (1 - P) * a = a * (1 - P) := by
    noncomm_ring [hPa]
  have hCompB : (1 - P) * b = b * (1 - P) := by
    noncomm_ring [hPb]
  have hPlusA : comm (conePlus P A) a = conePlus P (A * a - a * A) := by
    calc
      comm (conePlus P A) a =
          P * A * ((1 - P) * a) - (a * P) * A * (1 - P) := by
            unfold comm conePlus
            noncomm_ring
      _ = P * A * (a * (1 - P)) - (P * a) * A * (1 - P) := by
            rw [hCompA, hPa]
      _ = conePlus P (A * a - a * A) := by
            unfold conePlus
            noncomm_ring [hP]
  have hMinusA : comm (coneMinus P C) a = coneMinus P (C * a - a * C) := by
    calc
      comm (coneMinus P C) a =
          (1 - P) * C * (P * a) - a * (1 - P) * C * P := by
            unfold comm coneMinus
            noncomm_ring
      _ = (1 - P) * C * (a * P) - ((1 - P) * a) * C * P := by
            rw [hPa, hCompA]
      _ = coneMinus P (C * a - a * C) := by
            unfold coneMinus
            noncomm_ring [hP]
  have hPlusB : comm (conePlus P A') b = conePlus P (A' * b - b * A') := by
    calc
      comm (conePlus P A') b =
          P * A' * ((1 - P) * b) - (b * P) * A' * (1 - P) := by
            unfold comm conePlus
            noncomm_ring
      _ = P * A' * (b * (1 - P)) - (P * b) * A' * (1 - P) := by
            rw [hCompB, hPb]
      _ = conePlus P (A' * b - b * A') := by
            unfold conePlus
            noncomm_ring [hP]
  have hMinusB : comm (coneMinus P C') b = coneMinus P (C' * b - b * C') := by
    calc
      comm (coneMinus P C') b =
          (1 - P) * C' * (P * b) - b * (1 - P) * C' * P := by
            unfold comm coneMinus
            noncomm_ring
      _ = (1 - P) * C' * (b * P) - ((1 - P) * b) * C' * P := by
            rw [hPb, hCompB]
      _ = coneMinus P (C' * b - b * C') := by
            unfold coneMinus
            noncomm_ring [hP]
  have hFormA : comm (genPhi P A C) a =
      genPhi P (A * a - a * A) (C * a - a * C) := by
    calc
      comm (genPhi P A C) a =
          comm (conePlus P A) a + comm (coneMinus P C) a := by
            unfold comm genPhi
            noncomm_ring
      _ = genPhi P (A * a - a * A) (C * a - a * C) := by
            rw [hPlusA, hMinusA]
            rfl
  have hFormB : comm (genPhi P A' C') b =
      genPhi P (A' * b - b * A') (C' * b - b * C') := by
    calc
      comm (genPhi P A' C') b =
          comm (conePlus P A') b + comm (coneMinus P C') b := by
            unfold comm genPhi
            noncomm_ring
      _ = genPhi P (A' * b - b * A') (C' * b - b * C') := by
            rw [hPlusB, hMinusB]
            rfl
  rw [hFormA, hFormB]
  peirce_nf hP

omit hP in
/-- Unitary conjugation of an operator is the operator plus its algebraic
inner-fluctuation term. Only the displayed right-unitary law is used here. -/
theorem peirce_unitary_inner_fluctuation
    {D U : B} [StarRing B] (hU : U * star U = 1) :
    U * D * star U = D + U * comm D (star U) := by
  unfold comm
  calc
    U * D * star U = D + U * D * star U - D := by abel
    _ = D + (U * D * star U - (U * star U) * D) := by
      rw [hU, one_mul]
      abel
    _ = D + U * (D * star U - star U * D) := by noncomm_ring

omit hP in
/-- For self-adjoint `D`, the inner-fluctuation term is self-adjoint. -/
theorem peirce_unitary_inner_fluctuation_selfAdjoint
    {D U : B} [StarRing B] (hU : U * star U = 1) (hD : star D = D) :
    star (U * comm D (star U)) = U * comm D (star U) := by
  have hForm : U * comm D (star U) = U * D * star U - D := by
    unfold comm
    calc
      U * (D * star U - star U * D) = U * D * star U - U * star U * D := by
        noncomm_ring
      _ = U * D * star U - D := by rw [hU, one_mul]
  rw [hForm, star_sub]
  have hConj : star (U * D * star U) = U * D * star U := by
    simp only [star_mul, star_star, hD]
    rw [mul_assoc]
  rw [hConj, hD]

omit hP in
/-- Conjugation by an even unitary preserves the Peirce form of the two-wave
operator and conjugates both transition amplitudes independently. -/
theorem peirce_yukawa_unitary_covariance
    {U : B} [StarRing B]
    (hPU : P * U = U * P) (hPUstar : P * star U = star U * P)
    (A C : B) :
    U * genPhi P A C * star U =
      genPhi P (U * A * star U) (U * C * star U) := by
  have hCompU : U * (1 - P) = (1 - P) * U := by
    noncomm_ring [hPU]
  have hCompStar : (1 - P) * star U = star U * (1 - P) := by
    noncomm_ring [hPUstar]
  unfold genPhi conePlus coneMinus
  rw [mul_add, add_mul]
  congr 1
  · calc
      U * (P * A * (1 - P)) * star U = (U * P) * A * ((1 - P) * star U) := by
        noncomm_ring
      _ = (P * U) * A * (star U * (1 - P)) := by rw [hPU, hCompStar]
      _ = P * (U * A * star U) * (1 - P) := by noncomm_ring
  · calc
      U * ((1 - P) * C * P) * star U = (U * (1 - P)) * C * (P * star U) := by
        noncomm_ring
      _ = ((1 - P) * U) * C * (star U * P) := by rw [hCompU, hPUstar]
      _ = (1 - P) * (U * C * star U) * P := by noncomm_ring

omit hP in
/-- Conjugation by a two-sided unitary preserves ordered products. -/
theorem peirce_unitary_conjugation_mul
    {U X Y : B} [StarRing B] (hU : star U * U = 1) :
    (U * X * star U) * (U * Y * star U) = U * (X * Y) * star U := by
  calc
    (U * X * star U) * (U * Y * star U) =
        U * X * (star U * U) * Y * star U := by noncomm_ring
    _ = U * (X * Y) * star U := by
      rw [hU]
      simp only [mul_one]
      noncomm_ring

omit hP in
/-- The quartic Dirac polynomial is covariant under unitary conjugation. -/
theorem dirac_quartic_unitary_covariance
    {U D : B} [StarRing B] (hU : star U * U = 1) :
    diracQuarticPolynomial (U * D * star U) =
      U * diracQuarticPolynomial D * star U := by
  have hD2 := peirce_unitary_conjugation_mul hU (X := D) (Y := D)
  have hD4 := peirce_unitary_conjugation_mul hU (X := D * D) (Y := D * D)
  unfold diracQuarticPolynomial
  rw [hD2, hD4]
  noncomm_ring

omit hP in
/-- The shifted quadratic defect polynomial is covariant under two-sided
unitary conjugation, including its identity terms. -/
theorem dirac_higgs_unitary_covariance
    {U D : B} [StarRing B] (hU₁ : star U * U = 1)
    (hU₂ : U * star U = 1) :
    ( (U * D * star U) * (U * D * star U) -
        (2 : ℤ) • (1 : B)) *
      ((U * D * star U) * (U * D * star U) - 1) =
    U * ((D * D - (2 : ℤ) • (1 : B)) * (D * D - 1)) * star U := by
  have hD2 := peirce_unitary_conjugation_mul hU₁ (X := D) (Y := D)
  rw [hD2]
  have hShiftOne : U * (D * D - 1) * star U = U * (D * D) * star U - 1 := by
    noncomm_ring [hU₂]
  have hShiftTwo : U * (D * D - (2 : ℤ) • (1 : B)) * star U =
      U * (D * D) * star U - (2 : ℤ) • (1 : B) := by
    noncomm_ring [hU₂]
  calc
    (U * (D * D) * star U - (2 : ℤ) • (1 : B)) *
        (U * (D * D) * star U - 1) =
      (U * (D * D - (2 : ℤ) • (1 : B)) * star U) *
        (U * (D * D - 1) * star U) := by rw [← hShiftTwo, ← hShiftOne]
    _ = U * ((D * D - (2 : ℤ) • (1 : B)) * (D * D - 1)) * star U :=
      peirce_unitary_conjugation_mul hU₁

/-- The star-twisted Peirce reflection used for the two sign channels. -/
def peirceRealTwist (P X : B) [StarRing B] : B := invS P * star X * invS P

/-- If the cut is self-adjoint, the star-twisted Peirce reflection is an
involutive anti-automorphism of the ambient operator ring. -/
theorem peirce_real_twist_anti_involution [StarRing B]
    (hPstar : star P = P) (X Y : B) :
    peirceRealTwist P (peirceRealTwist P X) = X ∧
    peirceRealTwist P (X * Y) = peirceRealTwist P Y * peirceRealTwist P X ∧
    peirceRealTwist P (invS P) = invS P := by
  have hSstar : star (invS P) = invS P := by
    simp [invS, hPstar]
  have hSsq : invS P * invS P = 1 := peirce_chirality_involution hP
  have hUnit : star (invS P) * invS P = 1 := by
    rw [hSstar]
    exact hSsq
  refine ⟨?_, ?_, ?_⟩
  · unfold peirceRealTwist
    have hStarX : star (invS P * star X * invS P) =
        invS P * X * invS P := by
      rw [star_mul, star_mul, hSstar, star_star]
      exact (mul_assoc _ _ _).symm
    rw [hStarX]
    calc
      invS P * (invS P * X * invS P) * invS P =
          (invS P * invS P) * X * (invS P * invS P) := by noncomm_ring
      _ = (1 : B) * X * 1 := by rw [hSsq]
      _ = X := by simp
  · unfold peirceRealTwist
    rw [star_mul]
    calc
      invS P * (star Y * star X) * invS P =
          invS P * star Y * (invS P * invS P) * star X * invS P := by
            rw [hSsq]
            noncomm_ring
      _ = (invS P * star Y * invS P) *
          (invS P * star X * invS P) := by noncomm_ring
  · unfold peirceRealTwist
    rw [hSstar]
    calc
      invS P * invS P * invS P = (invS P * invS P) * invS P := by rw [mul_assoc]
      _ = (1 : B) * invS P := by rw [hSsq]
      _ = invS P := by rw [one_mul]

/-- Odd operators change sign under conjugation by the Peirce involution. -/
theorem peirce_odd_conjugation_neg (X : B)
    (hOdd : anticomm (invS P) X = 0) :
    invS P * X * invS P = -X := by
  have hS : invS P * invS P = 1 := peirce_chirality_involution hP
  have hOdd' : invS P * X + X * invS P = 0 := hOdd
  have hMul : invS P * X = -(X * invS P) :=
    add_eq_zero_iff_eq_neg.mp hOdd'
  calc
    invS P * X * invS P = -(X * invS P) * invS P := by rw [hMul]
    _ = -(X * (invS P * invS P)) := by noncomm_ring
    _ = -X := by rw [hS, mul_one]

/-- The star-twisted reflection negates a self-adjoint odd operator. -/
theorem peirce_real_twist_selfAdjoint_odd [StarRing B] (X : B)
    (hOdd : anticomm (invS P) X = 0) (hStar : star X = X) :
    peirceRealTwist P X = -X := by
  unfold peirceRealTwist
  rw [hStar]
  exact peirce_odd_conjugation_neg hP X hOdd

/-- The star-twisted reflection fixes a skew-adjoint odd operator. -/
theorem peirce_real_twist_skewAdjoint_odd [StarRing B] (X : B)
    (hOdd : anticomm (invS P) X = 0) (hStar : star X = -X) :
    peirceRealTwist P X = X := by
  unfold peirceRealTwist
  rw [hStar]
  calc
    invS P * (-X) * invS P = -(invS P * X * invS P) := by noncomm_ring
    _ = -(-X) := by rw [peirce_odd_conjugation_neg hP X hOdd]
    _ = X := neg_neg X

/-- The antisymmetric real-structure channel selects self-adjoint odd
operators by doubling and removes skew-adjoint odd operators. -/
def peirceRealHiggsChannel (P X : B) [StarRing B] : B := X - peirceRealTwist P X

/-- The symmetric real-structure channel selects skew-adjoint odd operators
by doubling and removes self-adjoint odd operators. -/
def peirceRealCurrentChannel (P X : B) [StarRing B] : B := X + peirceRealTwist P X

theorem peirce_real_structure_channel_selection [StarRing B] (X Y : B)
    (hXOdd : anticomm (invS P) X = 0) (hXStar : star X = X)
    (hYOdd : anticomm (invS P) Y = 0) (hYStar : star Y = -Y) :
    peirceRealHiggsChannel P X = (2 : ℤ) • X ∧
    peirceRealHiggsChannel P Y = 0 ∧
    peirceRealCurrentChannel P X = 0 ∧
    peirceRealCurrentChannel P Y = (2 : ℤ) • Y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [peirceRealHiggsChannel,
      peirce_real_twist_selfAdjoint_odd hP X hXOdd hXStar]
    simp only [sub_neg_eq_add, two_zsmul]
  · simp [peirceRealHiggsChannel,
      peirce_real_twist_skewAdjoint_odd hP Y hYOdd hYStar]
  · simp [peirceRealCurrentChannel,
      peirce_real_twist_selfAdjoint_odd hP X hXOdd hXStar]
  · rw [peirceRealCurrentChannel,
      peirce_real_twist_skewAdjoint_odd hP Y hYOdd hYStar, two_zsmul]

omit hP in
/-- The odd Peirce sector is stable under left and right multiplication by
elements commuting with the cut. -/
theorem peirce_odd_bimodule_closed (a X : B)
    (hEven : comm P a = 0) (hOdd : anticomm (invS P) X = 0) :
    anticomm (invS P) (a * X) = 0 ∧
      anticomm (invS P) (X * a) = 0 := by
  have hPa : P * a = a * P := by
    change P * a - a * P = 0 at hEven
    exact sub_eq_zero.mp hEven
  have hSa : invS P * a = a * invS P := by
    dsimp [invS]
    noncomm_ring [hPa]
  change invS P * X + X * invS P = 0 at hOdd
  constructor
  · change invS P * (a * X) + (a * X) * invS P = 0
    calc
      invS P * (a * X) + (a * X) * invS P =
          (invS P * a) * X + a * (X * invS P) := by
            rw [← mul_assoc (invS P) a X, mul_assoc a X (invS P)]
      _ = (a * invS P) * X + a * (X * invS P) := by rw [hSa]
      _ = a * (invS P * X) + a * (X * invS P) := by rw [mul_assoc]
      _ = a * (invS P * X + X * invS P) := by rw [mul_add]
      _ = 0 := by rw [hOdd, mul_zero]
  · change invS P * (X * a) + (X * a) * invS P = 0
    calc
      invS P * (X * a) + (X * a) * invS P =
          invS P * X * a + X * invS P * a := by
            noncomm_ring [hSa]
      _ = (invS P * X + X * invS P) * a := by rw [add_mul]
      _ = 0 := by rw [hOdd, zero_mul]

/-- A basic algebraic one-form term for the odd Peirce operator. -/
def peirceInnerOneFormTerm (P A C a b : B) : B :=
  a * comm (genPhi P A C) b

/-- If both coefficients commute with the cut, the algebraic one-form term
`a * [Φ, b]` remains in the odd Peirce sector. -/
theorem peirce_inner_one_form_term_is_odd (A C a b : B)
    (hA : comm P a = 0) (hB : comm P b = 0) :
    anticomm (invS P) (peirceInnerOneFormTerm P A C a b) = 0 := by
  unfold peirceInnerOneFormTerm
  exact (peirce_odd_bimodule_closed a (comm (genPhi P A C) b) hA
    (peirce_yukawa_commutator_is_odd hP A C b hB)).1

/-- Finite sums of algebraic one-form terms with even coefficients remain in
the odd Peirce sector. This is the finite algebraic closure result; it makes
no analytic claim about completed spaces of differential forms. -/
theorem peirce_finite_sum_inner_one_forms_is_odd {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (A C : B) (a b : ι → B)
    (hA : ∀ i ∈ s, comm P (a i) = 0)
    (hB : ∀ i ∈ s, comm P (b i) = 0) :
    anticomm (invS P)
      (∑ i ∈ s, peirceInnerOneFormTerm P A C (a i) (b i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [anticomm]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hiTerm := peirce_inner_one_form_term_is_odd hP A C (a i) (b i)
        (hA i (Finset.mem_insert_self i s))
        (hB i (Finset.mem_insert_self i s))
      have hsA : ∀ j ∈ s, comm P (a j) = 0 := by
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      have hsB : ∀ j ∈ s, comm P (b j) = 0 := by
        intro j hj
        exact hB j (Finset.mem_insert_of_mem hj)
      have hsTerm := ih hsA hsB
      change invS P * (peirceInnerOneFormTerm P A C (a i) (b i) +
          ∑ j ∈ s, peirceInnerOneFormTerm P A C (a j) (b j)) +
        (peirceInnerOneFormTerm P A C (a i) (b i) +
          ∑ j ∈ s, peirceInnerOneFormTerm P A C (a j) (b j)) * invS P = 0
      change invS P * peirceInnerOneFormTerm P A C (a i) (b i) +
          peirceInnerOneFormTerm P A C (a i) (b i) * invS P = 0 at hiTerm
      change invS P * (∑ j ∈ s, peirceInnerOneFormTerm P A C (a j) (b j)) +
          (∑ j ∈ s, peirceInnerOneFormTerm P A C (a j) (b j)) * invS P = 0 at hsTerm
      calc
        _ = (invS P * peirceInnerOneFormTerm P A C (a i) (b i) +
              peirceInnerOneFormTerm P A C (a i) (b i) * invS P) +
            (invS P * (∑ j ∈ s, peirceInnerOneFormTerm P A C (a j) (b j)) +
              (∑ j ∈ s, peirceInnerOneFormTerm P A C (a j) (b j)) * invS P) := by
                noncomm_ring
        _ = 0 := by rw [hiTerm, hsTerm, add_zero]

/-- The commutator of two operators odd under the Peirce grading is fixed by
the grading automorphism. This gives the next parity grade without identifying
fixedness with a block projection in rings with possible 2-torsion. -/
theorem peirce_odd_commutator_is_parity_fixed (X Y : B)
    (hX : anticomm (invS P) X = 0)
    (hY : anticomm (invS P) Y = 0) :
    parityConj P (comm X Y) = comm X Y := by
  have hS : invS P * invS P = 1 := peirce_chirality_involution hP
  have hXneg : parityConj P X = -X := by
    change invS P * X * invS P = -X
    have hX' : invS P * X + X * invS P = 0 := hX
    have hXmul : invS P * X = -(X * invS P) := add_eq_zero_iff_eq_neg.mp hX'
    calc
      invS P * X * invS P = (-(X * invS P)) * invS P := by rw [hXmul]
      _ = -(X * (invS P * invS P)) := by noncomm_ring
      _ = -X := by rw [hS, mul_one]
  have hYneg : parityConj P Y = -Y := by
    change invS P * Y * invS P = -Y
    have hY' : invS P * Y + Y * invS P = 0 := hY
    have hYmul : invS P * Y = -(Y * invS P) := add_eq_zero_iff_eq_neg.mp hY'
    calc
      invS P * Y * invS P = (-(Y * invS P)) * invS P := by rw [hYmul]
      _ = -(Y * (invS P * invS P)) := by noncomm_ring
      _ = -Y := by rw [hS, mul_one]
  calc
    parityConj P (comm X Y) = comm (parityConj P X) (parityConj P Y) := by
      change (parityConjRingEquiv hP) (X * Y - Y * X) =
        parityConj P X * parityConj P Y - parityConj P Y * parityConj P X
      rw [map_sub, map_mul, map_mul]
      change parityConj P X * parityConj P Y - parityConj P Y * parityConj P X = _
      rfl
    _ = comm X Y := by rw [hXneg, hYneg]; unfold comm; noncomm_ring

/-- The commutator obstruction of two finite sums of even-coefficient
one-forms lies in the parity-fixed grade. It is retained as a bracket; no
claim that it vanishes is imposed. -/
theorem peirce_finite_one_form_commutator_is_parity_fixed
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (A C : B)
    (a b : ι → B) (c d : κ → B)
    (ha : ∀ i ∈ s, comm P (a i) = 0)
    (hb : ∀ i ∈ s, comm P (b i) = 0)
    (hc : ∀ i ∈ t, comm P (c i) = 0)
    (hd : ∀ i ∈ t, comm P (d i) = 0) :
    let F := ∑ i ∈ s, peirceInnerOneFormTerm P A C (a i) (b i)
    let G := ∑ i ∈ t, peirceInnerOneFormTerm P A C (c i) (d i)
    parityConj P (comm F G) = comm F G := by
  dsimp
  exact peirce_odd_commutator_is_parity_fixed hP _ _
    (peirce_finite_sum_inner_one_forms_is_odd hP s A C a b ha hb)
    (peirce_finite_sum_inner_one_forms_is_odd hP t A C c d hc hd)

/-- Right-recursive powers of an element of the Peirce interaction. -/
def peirceOperatorPower : ℕ → B → B
  | 0, _ => 1
  | n + 1, x => peirceOperatorPower n x * x

/-- The metric interaction commutes with each of its boundary arrows. -/
theorem peirce_metric_commutes_with_arrows (A C : B) :
    genV P A C * conePlus P A = conePlus P A * genV P A C ∧
    genV P A C * coneMinus P C = coneMinus P C * genV P A C := by
  constructor <;>
    (simp only [genV, anticomm, conePlus, coneMinus]; peirce_nf hP)

/-- The powers of the metric commute with the grading and the boundary arrows. -/
theorem peirce_metric_power_commutations (n : ℕ) (A C : B) :
    invS P * peirceOperatorPower n (genV P A C) =
      peirceOperatorPower n (genV P A C) * invS P ∧
    peirceOperatorPower n (genV P A C) * conePlus P A =
      conePlus P A * peirceOperatorPower n (genV P A C) ∧
    peirceOperatorPower n (genV P A C) * coneMinus P C =
      coneMinus P C * peirceOperatorPower n (genV P A C) := by
  have hSV : invS P * genV P A C = genV P A C * invS P := by peirce_nf hP
  rcases peirce_metric_commutes_with_arrows hP A C with ⟨hVP, hVM⟩
  induction n with
  | zero => simp [peirceOperatorPower]
  | succ n ih =>
      simp only [peirceOperatorPower]
      rcases ih with ⟨ihS, ihP, ihM⟩
      refine ⟨?_, ?_, ?_⟩
      · calc
          invS P * (peirceOperatorPower n (genV P A C) * genV P A C) =
              (invS P * peirceOperatorPower n (genV P A C)) * genV P A C := by
                rw [mul_assoc]
          _ = (peirceOperatorPower n (genV P A C) * invS P) * genV P A C := by
                rw [ihS]
          _ = peirceOperatorPower n (genV P A C) *
                (invS P * genV P A C) := by rw [mul_assoc]
          _ = peirceOperatorPower n (genV P A C) *
                (genV P A C * invS P) := by rw [hSV]
          _ = (peirceOperatorPower n (genV P A C) * genV P A C) * invS P := by
                rw [mul_assoc]
      · calc
          (peirceOperatorPower n (genV P A C) * genV P A C) * conePlus P A =
              peirceOperatorPower n (genV P A C) *
                (genV P A C * conePlus P A) := by rw [mul_assoc]
          _ = peirceOperatorPower n (genV P A C) *
                (conePlus P A * genV P A C) := by rw [hVP]
          _ = (peirceOperatorPower n (genV P A C) * conePlus P A) *
                genV P A C := by rw [mul_assoc]
          _ = (conePlus P A * peirceOperatorPower n (genV P A C)) *
                genV P A C := by rw [ihP]
          _ = conePlus P A *
                (peirceOperatorPower n (genV P A C) * genV P A C) := by
                rw [mul_assoc]
      · calc
          (peirceOperatorPower n (genV P A C) * genV P A C) * coneMinus P C =
              peirceOperatorPower n (genV P A C) *
                (genV P A C * coneMinus P C) := by rw [mul_assoc]
          _ = peirceOperatorPower n (genV P A C) *
                (coneMinus P C * genV P A C) := by rw [hVM]
          _ = (peirceOperatorPower n (genV P A C) * coneMinus P C) *
                genV P A C := by rw [mul_assoc]
          _ = (coneMinus P C * peirceOperatorPower n (genV P A C)) *
                genV P A C := by rw [ihM]
          _ = coneMinus P C *
                (peirceOperatorPower n (genV P A C) * genV P A C) := by
                rw [mul_assoc]

/-- Every positive chiral density is the explicit commutator
`[V^n N₊, N₋]`. -/
theorem peirce_chiral_power_is_commutator (n : ℕ) (A C : B) :
    invS P * peirceOperatorPower (n + 1) (genV P A C) =
      comm (peirceOperatorPower n (genV P A C) * conePlus P A)
        (coneMinus P C) := by
  rcases peirce_metric_power_commutations hP n A C with ⟨hS, hPlus, hMinus⟩
  have hSV : invS P * genV P A C = genSig P A C := by peirce_nf hP
  calc
    invS P * peirceOperatorPower (n + 1) (genV P A C) =
        peirceOperatorPower n (genV P A C) * genSig P A C := by
          simp only [peirceOperatorPower]
          rw [← mul_assoc, hS, mul_assoc, hSV]
    _ = comm (peirceOperatorPower n (genV P A C) * conePlus P A)
          (coneMinus P C) := by
        unfold comm genSig
        have hterm : peirceOperatorPower n (genV P A C) *
            (coneMinus P C * conePlus P A) =
            coneMinus P C * (peirceOperatorPower n (genV P A C) * conePlus P A) := by
          calc
            _ = (peirceOperatorPower n (genV P A C) * coneMinus P C) *
                conePlus P A := by rw [mul_assoc]
            _ = (coneMinus P C * peirceOperatorPower n (genV P A C)) *
                conePlus P A := by rw [hMinus]
            _ = _ := by rw [mul_assoc]
        calc
          peirceOperatorPower n (genV P A C) *
              (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) =
              peirceOperatorPower n (genV P A C) * conePlus P A * coneMinus P C -
                coneMinus P C * (peirceOperatorPower n (genV P A C) * conePlus P A) := by
            rw [mul_sub, mul_assoc, hterm]
          _ = comm (peirceOperatorPower n (genV P A C) * conePlus P A)
              (coneMinus P C) := rfl

/-- A cyclic additive functional annihilates every positive chiral power
density, by the exact commutator formula. -/
theorem peirce_chiral_power_cyclic_trace_zero
    {R : Type*} [Ring R] (τ : B → R)
    (hSub : ∀ X Y : B, τ (X - Y) = τ X - τ Y)
    (hCyc : ∀ X Y : B, τ (X * Y) = τ (Y * X))
    (n : ℕ) (A C : B) :
    τ (invS P * peirceOperatorPower (n + 1) (genV P A C)) = 0 := by
  rw [peirce_chiral_power_is_commutator hP n A C]
  unfold comm
  rw [hSub, hCyc, sub_self]

/-- The quartic Dirac polynomial splits into twice the Peirce interaction
and the defect of that interaction. -/
theorem dirac_quartic_polynomial_split (A C : B) :
    diracQuarticPolynomial (peirceMassDirac P A C) =
      (2 : ℤ) • genV P A C + idempotencyDefect (genV P A C) := by
  rw [diracQuarticPolynomial, peirce_mass_dirac_square hP]
  dsimp [idempotencyDefect]
  noncomm_ring

/-- The shifted quadratic polynomial in the massive Dirac square is exactly
the defect of the Peirce interaction. -/
theorem dirac_higgs_polynomial_is_operator_defect (A C : B) :
    (peirceMassDirac P A C * peirceMassDirac P A C -
        (2 : ℤ) • (1 : B)) *
      (peirceMassDirac P A C * peirceMassDirac P A C - 1) =
      idempotencyDefect (genV P A C) := by
  rw [peirce_mass_dirac_square hP]
  dsimp [idempotencyDefect]
  simp only [two_zsmul]
  noncomm_ring

/-- The metric defect separates into the defects of its two ordered Peirce
round-trip corners. -/
theorem peirce_metric_defect_split (A C : B) :
    idempotencyDefect (genV P A C) =
      idempotencyDefect (qgtPlus P A C) +
        idempotencyDefect (qgtMinus P A C) := by
  simp only [idempotencyDefect, genV, anticomm, qgtPlus, qgtMinus]
  peirce_nf hP

/-- Causal synthesis: the Peirce square law precedes the two Dirac squares,
which in turn determine the quartic and shifted defect polynomials. -/
theorem peirce_dirac_polynomial_causal_synthesis (A C : B) :
    peirceMassDirac P A C * peirceMassDirac P A C = 1 + genV P A C ∧
    peirceChiralDirac P A C * peirceChiralDirac P A C = 1 - genV P A C ∧
    idempotencyDefect (P + genPhi P A C) =
      -(comm P (P + genPhi P A C) * comm P (P + genPhi P A C)) ∧
    diracQuarticPolynomial (peirceMassDirac P A C) =
      (2 : ℤ) • genV P A C + idempotencyDefect (genV P A C) ∧
    idempotencyDefect (genV P A C) =
      idempotencyDefect (qgtPlus P A C) +
        idempotencyDefect (qgtMinus P A C) ∧
    comm (peirceMassDirac P A C)
      (comm (peirceMassDirac P A C) (genJ P A C)) =
        (4 : ℤ) • ((1 + genV P A C) * genJ P A C) ∧
    (peirceMassDirac P A C * peirceMassDirac P A C -
        (2 : ℤ) • (1 : B)) *
      (peirceMassDirac P A C * peirceMassDirac P A C - 1) =
      idempotencyDefect (genV P A C) := by
  exact ⟨peirce_mass_dirac_square hP A C,
    peirce_chiral_dirac_square hP A C,
    transfer_defect_eq_neg_comm_square hP A C,
    dirac_quartic_polynomial_split hP A C,
    peirce_metric_defect_split hP A C,
    grading_phi_double_comm_j hP A C,
    dirac_higgs_polynomial_is_operator_defect hP A C⟩

/-- The degree-two crossed commutator generated by two independent
connections. -/
def diracMixedCommutator₂ (P A₁ C₁ A₂ C₂ : B) : B :=
  comm (coneMinus P C₁) (conePlus P A₂) -
    comm (coneMinus P C₂) (conePlus P A₁)

/-- The next, Jordan-symmetric contribution paired with the crossed
commutator at degree two. -/
def diracMixedJordan₂ (P A₁ C₁ A₂ C₂ : B) : B :=
  anticomm (coneMinus P C₁) (conePlus P A₂) -
    anticomm (coneMinus P C₂) (conePlus P A₁)

/-- The mixed square splits into the two individual quadratic terms, the
commutator cross-term, and its second-order Peirce obstruction. -/
theorem dirac_mixed_square_with_obstruction (A₁ C₁ A₂ C₂ : B) :
    (genPhi P A₁ C₁ + genJ P A₂ C₂) *
      (genPhi P A₁ C₁ + genJ P A₂ C₂) =
      genV P A₁ C₁ - genV P A₂ C₂ -
        (comm (conePlus P A₁) (coneMinus P C₂) -
          comm (conePlus P A₂) (coneMinus P C₁)) +
      diracMixedCommutator₂ P A₁ C₁ A₂ C₂ +
        diracMixedJordan₂ P A₁ C₁ A₂ C₂ := by
  simp only [diracMixedCommutator₂, diracMixedJordan₂]
  peirce_nf hP

/-- The crossed commutator is an even Peirce component: its odd projection
vanishes. -/
theorem dirac_mixed_commutator₂_even (A₁ C₁ A₂ C₂ : B) :
    evenGrade P (diracMixedCommutator₂ P A₁ C₁ A₂ C₂) =
        diracMixedCommutator₂ P A₁ C₁ A₂ C₂ ∧
      oddGrade P (diracMixedCommutator₂ P A₁ C₁ A₂ C₂) = 0 := by
  simp only [diracMixedCommutator₂]
  constructor <;> peirce_nf hP

omit hP
variable [StarRing B]

/-- With a self-adjoint idempotent and the adjoint reverse wave, the
two-wave Peirce operator is self-adjoint. -/
theorem peirce_yukawa_self_adjoint
    (hPs : star P = P) (A : B) :
    star (genPhi P A (star A)) = genPhi P A (star A) := by
  have hPlus : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPs, mul_assoc]
  have hMinus : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hPlus, star_star]
  unfold genPhi
  rw [star_add, hPlus, hMinus, add_comm]

end InfoGeometry.OperatorAlgebra.PeirceSpine
