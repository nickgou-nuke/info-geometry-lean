/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.LieJordanDuality
import InfoGeometry.Algebra.PeirceDeWittChiralSplit

/-!
# The Peirce quartet as Lie--Jordan superoperator projectors

The four corners are the repository's existing `peirce11`, `peirce10`,
`peirce01`, and `peirce00`. The Boolean-indexed bundled maps add a uniform
composition and multiplication interface, not a second corner carrier.
The complementary-corner formula retains the source's negative double commutator.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution

open LieJordanDuality

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- A bundled corner projector: multiplication on both sides, in the original algebra. -/
def corner (p : A) (i j : Bool) : Module.End R A :=
  LinearMap.mulLeftRight R
    ((if i then p else compIdempotent p), (if j then p else compIdempotent p))

@[simp] theorem corner_apply (p X : A) (i j : Bool) :
    corner R p i j X =
      (if i then p else compIdempotent p) * X *
        (if j then p else compIdempotent p) := rfl

@[simp] theorem corner_tt (p X : A) : corner R p true true X = peirce11 p X := rfl
@[simp] theorem corner_tf (p X : A) : corner R p true false X = peirce10 p X := rfl
@[simp] theorem corner_ft (p X : A) : corner R p false true X = peirce01 p X := rfl
@[simp] theorem corner_ff (p X : A) : corner R p false false X = peirce00 p X := rfl

/-- This one formula covers all four products of the endpoint idempotents. -/
theorem endpoint_mul {p : A} (hp : p * p = p) (i j : Bool) :
    (if i then p else compIdempotent p) * (if j then p else compIdempotent p) =
      if i = j then (if i then p else compIdempotent p) else 0 := by
  cases i <;> cases j <;>
    simp [compIdempotent, mul_sub, sub_mul, hp]

/-- All sixteen compositions of the four linear projectors. -/
theorem corner_comp {p : A} (hp : p * p = p) (i j k l : Bool) :
    corner R p i j * corner R p k l =
      if i = k ∧ j = l then corner R p i j else 0 := by
  ext X
  change (if i then p else compIdempotent p) *
      ((if k then p else compIdempotent p) * X *
        (if l then p else compIdempotent p)) *
      (if j then p else compIdempotent p) = _
  have hfactor :
      (if i then p else compIdempotent p) *
        ((if k then p else compIdempotent p) * X *
          (if l then p else compIdempotent p)) *
        (if j then p else compIdempotent p) =
      ((if i then p else compIdempotent p) *
        (if k then p else compIdempotent p)) * X *
        ((if l then p else compIdempotent p) *
          (if j then p else compIdempotent p)) := by simp only [mul_assoc]
  rw [hfactor, endpoint_mul hp, endpoint_mul hp]
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [hik, hjl, eq_comm, corner_apply]

/-- Resolution of the identity as actual endomorphisms. -/
theorem corner_sum (p : A) :
    corner R p true true + corner R p true false +
      corner R p false true + corner R p false false = 1 := by
  ext X
  exact peirce_decomposition_sum p X

/-- The sixteen-cell Peirce multiplication table, with no commuting inputs. -/
theorem corner_mul {p : A} (hp : p * p = p) (i j k l : Bool) (X Y : A) :
    corner R p i j X * corner R p k l Y =
      if j = k then corner R p i l (X * (if j then p else compIdempotent p) * Y)
      else 0 := by
  have hfactor : corner R p i j X * corner R p k l Y =
      (if i then p else compIdempotent p) * X *
        ((if j then p else compIdempotent p) *
          (if k then p else compIdempotent p)) * Y *
        (if l then p else compIdempotent p) := by
    simp only [corner_apply, mul_assoc]
  rw [hfactor, endpoint_mul hp]
  by_cases h : j = k <;> simp [h, corner_apply, mul_assoc]

/-- Exact double commutator; this is not a spectral approximation. -/
theorem ad_square {p : A} (hp : p * p = p) (X : A) :
    ad R p (ad R p X) = p * X + X * p - 2 • (p * X * p) := by
  simp only [ad_apply, two_nsmul]
  calc
    _ = (p * p) * X + X * (p * p) - (p * X * p + p * X * p) := by
      noncomm_ring
    _ = _ := by rw [hp]

theorem twice_peirce11 {p : A} (hp : p * p = p) (X : A) :
    2 • peirce11 p X = jordan R p X - ad R p (ad R p X) := by
  rw [ad_square R hp]
  simp only [jordan_apply, peirce11, two_nsmul]
  noncomm_ring

/-- The source's negative double-commutator sign is essential. -/
theorem twice_peirce00 {p : A} (hp : p * p = p) (X : A) :
    2 • peirce00 p X = 2 • X - jordan R p X - ad R p (ad R p X) := by
  rw [ad_square R hp]
  simp only [jordan_apply, peirce00, compIdempotent, two_nsmul]
  noncomm_ring

theorem twice_peirce10 {p : A} (hp : p * p = p) (X : A) :
    2 • peirce10 p X = ad R p (ad R p X) + ad R p X := by
  rw [ad_square R hp]
  simp only [ad_apply, peirce10, compIdempotent, two_nsmul]
  noncomm_ring

theorem twice_peirce01 {p : A} (hp : p * p = p) (X : A) :
    2 • peirce01 p X = ad R p (ad R p X) - ad R p X := by
  rw [ad_square R hp]
  simp only [ad_apply, peirce01, compIdempotent, two_nsmul]
  noncomm_ring

/-- Regression against an incorrect positive-sign variant of the source formula. -/
theorem complementary_plus_sign_defect {p : A} (hp : p * p = p) (X : A) :
    2 • peirce00 p X -
      (2 • X - jordan R p X + ad R p (ad R p X)) =
        -(2 • ad R p (ad R p X)) := by
  rw [twice_peirce00 R hp]
  simp only [two_nsmul]
  abel

/-- The double commutator is exactly the already-owned odd projection. -/
theorem ad_square_eq_oddPart {p : A} (hp : p * p = p) (X : A) :
    ad R p (ad R p X) =
      InfoGeometry.Algebra.PeirceDeWittChiralSplit.oddPart p X := by
  rw [ad_square R hp]
  simp only [InfoGeometry.Algebra.PeirceDeWittChiralSplit.oddPart,
    peirce10, peirce01, compIdempotent, two_nsmul]
  noncomm_ring

/-- The actual simultaneous Lie/Jordan action on every corner. -/
theorem corner_joint_action {p : A} (hp : p * p = p) (i j : Bool) (X : A) :
    ad R p (corner R p i j X) =
      (if i then corner R p i j X else 0) - (if j then corner R p i j X else 0) ∧
    jordan R p (corner R p i j X) =
      (if i then corner R p i j X else 0) + (if j then corner R p i j X else 0) := by
  have hn (x : A) : p * (p * x) = p * x := by rw [← mul_assoc, hp]
  cases i <;> cases j <;> constructor <;>
    simp only [corner_apply, ad_apply, jordan_apply, Bool.false_eq_true,
      ite_false, ite_true, compIdempotent] <;> noncomm_ring [hp, hn]

/-- The primal corner readout uses the same generator twice. -/
theorem primal_ad_corner {p : A} (hp : p * p = p) (X : A) :
    dualPlus R p p (ad R p X) = 2 • peirce10 p X := by
  simp only [dualPlus_apply, ad_apply, peirce10, compIdempotent, two_nsmul]
  have hn (x : A) : p * (p * x) = p * x := by rw [← mul_assoc, hp]
  noncomm_ring [hp, hn]

/-- For the defined negative Jordan perturbation this sign is positive too. -/
theorem dual_ad_corner {p : A} (hp : p * p = p) (X : A) :
    dualMinus R p p (ad R p X) = 2 • peirce01 p X := by
  simp only [dualMinus_apply, ad_apply, peirce01, compIdempotent, two_nsmul]
  have hn (x : A) : p * (p * x) = p * x := by rw [← mul_assoc, hp]
  noncomm_ring [hp, hn]

/-- Corner extraction commutes with every algebra homomorphism. -/
theorem map_corner {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (p X : A) (i j : Bool) :
    f (corner R p i j X) = corner R (f p) i j (f X) := by
  cases i <;> cases j <;>
    simp [corner_apply, compIdempotent, map_mul, map_sub, map_one]

end InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution
