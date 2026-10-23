/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Canonical Krein--Kramers alternatives

These lemmas isolate the ring-theoretic content behind Kramers and Krein
counterexamples.  They use arbitrary involutive associative rings and do not
depend on a coordinate model.
-/

namespace InfoGeometry.Canonical.KreinKramersAlternatives

variable {A : Type*} [Ring A] [StarRing A]

def jordanProd (x y : A) : A := x * y + y * x

def lieBracket (x y : A) : A := x * y - y * x

def kreinQuadraticForm (j x : A) : A := star x * j * x

def kreinAdjoint (j x : A) : A := j * star x * j

structure IsKreinFundamentalSymmetry (j : A) : Prop where
  selfAdjoint : star j = j
  sq_eq_one : j * j = 1

structure IsKramersOperator (t : A) : Prop where
  isometry : star t * t = 1
  sq_eq_neg_one : t * t = -1

theorem kreinAdjoint_involutive {j : A} (hJ : IsKreinFundamentalSymmetry j)
    (x : A) : kreinAdjoint j (kreinAdjoint j x) = x := by
  unfold kreinAdjoint
  rw [star_mul, star_mul, hJ.selfAdjoint, star_star]
  calc
    j * (j * (x * j)) * j = (j * j) * x * (j * j) := by noncomm_ring
    _ = x := by rw [hJ.sq_eq_one, one_mul, mul_one]

theorem kreinAdjoint_mul_reverse {j : A} (hJ : IsKreinFundamentalSymmetry j)
    (x y : A) :
    kreinAdjoint j (x * y) = kreinAdjoint j y * kreinAdjoint j x := by
  unfold kreinAdjoint
  rw [star_mul]
  calc
    j * (star y * star x) * j =
        j * star y * (j * j) * star x * j := by rw [hJ.sq_eq_one]; noncomm_ring
    _ = (j * star y * j) * (j * star x * j) := by noncomm_ring

theorem kreinQuadraticForm_selfAdjoint {j : A} (hJ : IsKreinFundamentalSymmetry j)
    (x : A) : star (kreinQuadraticForm j x) = kreinQuadraticForm j x := by
  unfold kreinQuadraticForm
  rw [star_mul, star_mul, star_star, hJ.selfAdjoint, mul_assoc]

theorem kramers_skew_adjoint {t : A} (hT : IsKramersOperator t) :
    star t = -t := by
  calc
    star t = star t * 1 := (mul_one (star t)).symm
    _ = star t * (-(t * t)) := by rw [hT.sq_eq_neg_one, neg_neg]
    _ = -(star t * t * t) := by noncomm_ring
    _ = -t := by rw [hT.isometry, one_mul]

theorem kramers_pair_orthogonal {t : A} (hT : IsKramersOperator t) (x : A) :
    star x * (t * x) + star (t * x) * x = 0 := by
  rw [star_mul]
  have hstar : star t = -t := kramers_skew_adjoint hT
  rw [hstar]
  noncomm_ring

/-- The failure of quadratic sign reversal is the sandwich of the
anticommutator defect. Only ordinary isometry is required; neither a
quaternionic square nor any condition on the form operator is used. -/
theorem quadratic_sign_flip_defect {t : A} (ht : star t * t = 1) (j x : A) :
    kreinQuadraticForm j (t * x) + kreinQuadraticForm j x =
      star x * (star t * jordanProd j t) * x := by
  unfold kreinQuadraticForm jordanProd
  rw [star_mul]
  calc
    star x * star t * j * (t * x) + star x * j * x =
        star x * (star t * j * t + j) * x := by noncomm_ring
    _ = star x * (star t * j * t + (star t * t) * j) * x := by
      rw [ht, one_mul]
    _ = star x * (star t * (j * t + t * j)) * x := by noncomm_ring

/-- Under a two-sided unitary, reversal of the operator-valued quadratic
form on every ring element is exactly anticommutation with its form operator.
There is no nonzero-signature or positivity conclusion. -/
theorem quadratic_sign_flip_iff_anticommute_of_unitary {t : A}
    (hleft : star t * t = 1) (hright : t * star t = 1) (j : A) :
    (∀ x : A, kreinQuadraticForm j (t * x) = -kreinQuadraticForm j x) ↔
      jordanProd j t = 0 := by
  constructor
  · intro h
    have hz : kreinQuadraticForm j (t * 1) + kreinQuadraticForm j 1 = 0 := by
      rw [h 1, neg_add_cancel]
    rw [quadratic_sign_flip_defect hleft] at hz
    simp only [star_one, one_mul, mul_one] at hz
    have hc := congrArg (fun y => t * y) hz
    simpa only [← mul_assoc, hright, one_mul, mul_zero] using hc
  · intro h x
    apply eq_neg_of_add_eq_zero_left
    rw [quadratic_sign_flip_defect hleft, h, mul_zero, mul_zero, zero_mul]

theorem kramers_krein_signature_flip {t : A} (hT : IsKramersOperator t)
    (j x : A) (hanti : jordanProd j t = 0) :
    kreinQuadraticForm j (t * x) = -kreinQuadraticForm j x := by
  have h_tj : t * j = -j * t := by
    unfold jordanProd at hanti
    calc
      t * j = (j * t + t * j) - j * t := by abel
      _ = 0 - j * t := by rw [hanti]
      _ = -j * t := by noncomm_ring
  unfold kreinQuadraticForm
  rw [star_mul]
  have hstar : star t = -t := kramers_skew_adjoint hT
  rw [hstar]
  calc
    (star x * -t) * j * (t * x) =
        -(star x * (t * j) * t * x) := by noncomm_ring
    _ = -(star x * (-j * t) * t * x) := by rw [h_tj]
    _ = star x * j * (t * t) * x := by noncomm_ring
    _ = -(star x * j * x) := by rw [hT.sq_eq_neg_one]; noncomm_ring

theorem centralizer_closed_under_mul_and_star
    (delta x y : A) (hdelta : star delta = delta)
    (hx : lieBracket delta x = 0) (hy : lieBracket delta y = 0) :
    lieBracket delta (x * y) = 0 ∧ lieBracket delta (star x) = 0 := by
  have hx' : delta * x = x * delta := sub_eq_zero.mp hx
  have hy' : delta * y = y * delta := sub_eq_zero.mp hy
  constructor
  · unfold lieBracket
    calc
      delta * (x * y) - (x * y) * delta =
          (delta * x) * y - x * (y * delta) := by noncomm_ring
      _ = x * (delta * y) - x * (y * delta) := by rw [hx']; noncomm_ring
      _ = 0 := by rw [hy', sub_self]
  · unfold lieBracket
    calc
      delta * star x - star x * delta =
          star (x * delta) - star (delta * x) := by rw [star_mul, star_mul, hdelta]
      _ = 0 := by rw [hx', sub_self]

end InfoGeometry.Canonical.KreinKramersAlternatives
