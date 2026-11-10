/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.SquareZeroPair
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Rigidity of square-zero operators paired with their C-star adjoints

For a square-zero operator `a`, a single test of the inner commutator
`[a, star a]` on `a` detects whether `a` vanishes. Consequently the two
native inner derivations commute exactly when the original operator is zero.

The C-star norm supplies properness of the adjoint. The coefficient field
has characteristic zero so that doubling can be cancelled. Neither
completeness nor finite dimension is required, and no ambient commutativity
or normalized partial-isometry equation is assumed.

The Peirce corollaries use the existing directed corners. They concern an
adjoint-paired corner in a positive C-star representation; they do not apply
to an arbitrary pair of square-zero elements or an indefinite involution.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroCStarRigidity

attribute [local instance 100] LieRing.ofAssociativeRing

section Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- Square-zero removes the two same-side products from the double bracket. -/
theorem square_zero_double_lie_star {a : A} (ha : a * a = 0) :
    ⁅⁅a, star a⁆, a⁆ = (2 : ℕ) • (a * star a * a) := by
  have haa (x : A) : a * (a * x) = 0 := by
    rw [← mul_assoc, ha, zero_mul]
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring [ha, haa]

end Ring

section CStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- C-star properness detects a zero triple product without nilpotency. -/
theorem self_mul_star_mul_self_eq_zero_iff (a : A) :
    a * star a * a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (CStarRing.star_mul_self_eq_zero_iff a).mp
    apply (CStarRing.star_mul_self_eq_zero_iff (star a * a)).mp
    simpa only [star_mul, star_star, mul_assoc, mul_zero] using
      congrArg (fun x : A => star a * x) h
  · rintro rfl
    simp

/-- A nonzero square-zero operator has a nonzero adjoint Gram sum. -/
theorem square_zero_gram_eq_zero_iff {a : A} (ha : a * a = 0) :
    a * star a + star a * a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (self_mul_star_mul_self_eq_zero_iff a).mp
    have hmul := congrArg (fun x : A => x * a) h
    simpa only [add_mul, mul_assoc, ha, mul_zero, add_zero, zero_mul] using hmul
  · rintro rfl
    simp

/-- The coupled square has the same exact zero criterion as its wing. -/
theorem square_zero_coupled_square_eq_zero_iff {a : A} (ha : a * a = 0) :
    (a + star a) * (a + star a) = 0 ↔ a = 0 := by
  have hstar : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star ha
  rw [PeirceSuperoperators.square_zero_pair_sum_sq ha hstar]
  exact square_zero_gram_eq_zero_iff ha

/-- Vanishing on the original square-zero operator already detects zero. -/
theorem square_zero_double_lie_star_eq_zero_iff
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] [Algebra 𝕜 A]
    {a : A} (ha : a * a = 0) :
    ⁅⁅a, star a⁆, a⁆ = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (self_mul_star_mul_self_eq_zero_iff a).mp
    have ht : (2 : 𝕜) • (a * star a * a) = 0 := by
      simpa only [two_smul, two_nsmul] using
        (square_zero_double_lie_star ha).symm.trans h
    exact (smul_eq_zero.mp ht).resolve_left two_ne_zero
  · rintro rfl
    simp

/-- Native inner derivations commute exactly when the square-zero wing is zero. -/
theorem square_zero_ad_commutator_eq_zero_iff
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] [Algebra 𝕜 A]
    {a : A} (ha : a * a = 0) :
    ⁅LieAlgebra.ad 𝕜 A a, LieAlgebra.ad 𝕜 A (star a)⁆ = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (square_zero_double_lie_star_eq_zero_iff 𝕜 ha).mp
    have had : LieAlgebra.ad 𝕜 A ⁅a, star a⁆ = 0 := by
      rw [(LieAlgebra.ad 𝕜 A).map_lie]
      exact h
    simpa only [LieAlgebra.ad_apply, LinearMap.zero_apply] using
      congrArg (fun D : Module.End 𝕜 A => D a) had
  · rintro rfl
    simp

/-- In the positive adjoint-paired setting, zero mixed curvature is equivalent
to a zero Gram operator. This implication requires the C-star hypotheses. -/
theorem square_zero_ad_commutator_eq_zero_iff_gram
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] [Algebra 𝕜 A]
    {a : A} (ha : a * a = 0) :
    ⁅LieAlgebra.ad 𝕜 A a, LieAlgebra.ad 𝕜 A (star a)⁆ = 0 ↔
      a * star a + star a * a = 0 :=
  (square_zero_ad_commutator_eq_zero_iff 𝕜 ha).trans
    (square_zero_gram_eq_zero_iff ha).symm

open PeirceSpine

/-- The C-star criterion applies to the repository's existing Peirce corners. -/
theorem peirce_ad_commutator_eq_zero_iff
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] [Algebra 𝕜 A]
    {P : A} (hP : P * P = P) (hPs : star P = P) (X : A) :
    ⁅LieAlgebra.ad 𝕜 A (conePlus P X),
      LieAlgebra.ad 𝕜 A (coneMinus P (star X))⁆ = 0 ↔
      conePlus P X = 0 := by
  have hstar : star (conePlus P X) = coneMinus P (star X) := by
    simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc]
  rw [← hstar]
  exact square_zero_ad_commutator_eq_zero_iff 𝕜 (conePlus_mul_conePlus hP X X)

/-- The exact Peirce form of the curvature/Gram vanishing equivalence. -/
theorem peirce_ad_commutator_eq_zero_iff_genV
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] [Algebra 𝕜 A]
    {P : A} (hP : P * P = P) (hPs : star P = P) (X : A) :
    ⁅LieAlgebra.ad 𝕜 A (conePlus P X),
      LieAlgebra.ad 𝕜 A (coneMinus P (star X))⁆ = 0 ↔
      genV P X (star X) = 0 := by
  have hstar : star (conePlus P X) = coneMinus P (star X) := by
    simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc]
  simpa only [genV, anticomm, ← hstar] using
    square_zero_ad_commutator_eq_zero_iff_gram 𝕜 (conePlus_mul_conePlus hP X X)

end CStar

end InfoGeometry.OperatorAlgebra.SquareZeroCStarRigidity
