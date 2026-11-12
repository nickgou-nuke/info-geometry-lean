/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Ordered star pairings and Peirce factorization

The carrier is an arbitrary associative star ring. The ordered pairing
`q * star k` is additive in each input and transforms by ordered left and
right factors. Its doubled self/skew sum uses the existing `digracSym` and
`digracImb`; no division by two, positivity, or polar decomposition is used.

The existing Peirce multiplication laws give the pairing factorization for
a self-adjoint idempotent. A form-twisted pairing is transported by the
actual star-congruence equation. Concrete preserving units are constructed
in the separate star-form owners.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceAffinity

open PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]

/-- The ordered operator-valued star pairing. -/
def affinity (q k : B) : B := q * star k

@[simp]
theorem affinity_star (q k : B) : star (affinity q k) = affinity k q := by
  simp only [affinity, star_mul, star_star]

theorem affinity_add_left (q₁ q₂ k : B) :
    affinity (q₁ + q₂) k = affinity q₁ k + affinity q₂ k := by
  simp only [affinity, add_mul]

theorem affinity_add_right (q k₁ k₂ : B) :
    affinity q (k₁ + k₂) = affinity q k₁ + affinity q k₂ := by
  simp only [affinity, star_add, mul_add]

/-- Outer factors stay on their respective sides; no centrality is assumed. -/
theorem affinity_outer_mul (a b q k : B) :
    affinity (a * q) (b * k) = a * affinity q k * star b := by
  simp only [affinity, star_mul, mul_assoc]

/-- Right multipliers contribute their ordered star pairing in the middle. -/
theorem affinity_right_mul (q k u v : B) :
    affinity (q * u) (k * v) = q * (u * star v) * star k := by
  simp only [affinity, star_mul, mul_assoc]

/-- A stated biorthogonality equation suffices for invariance. -/
theorem affinity_biorthogonal (q k u v : B) (huv : u * star v = 1) :
    affinity (q * u) (k * v) = affinity q k := by
  simpa only [huv, mul_one, affinity] using affinity_right_mul q k u v

/-- Existing self-adjoint sums become the two ordered affinity directions. -/
theorem digracSym_affinity (q k : B) :
    digracSym (affinity q k) = affinity q k + affinity k q := by
  rw [digracSym, affinity_star]

/-- Existing skew-adjoint differences retain the orientation of the pair. -/
theorem digracImb_affinity (q k : B) :
    digracImb (affinity q k) = affinity q k - affinity k q := by
  rw [digracImb, affinity_star]

theorem digracSym_affinity_isSelfAdjoint (q k : B) :
    IsSelfAdjoint (digracSym (affinity q k)) :=
  IsSelfAdjoint.add_star_self (affinity q k)

theorem digracImb_affinity_mem_skewAdjoint (q k : B) :
    digracImb (affinity q k) ∈ skewAdjoint B := by
  change star (digracImb (affinity q k)) = -digracImb (affinity q k)
  simp only [digracImb, star_sub, star_star, neg_sub]

/-- Reconstruction is doubled, with no inverse of two assumed. -/
theorem affinity_doubled_split (q k : B) :
    digracSym (affinity q k) + digracImb (affinity q k) =
      (2 : ℕ) • affinity q k := by
  simp only [digracSym, digracImb, two_nsmul]
  abel

/-- Star commutes with the existing diagonal projection of a self-adjoint cut. -/
theorem star_evenGrade {p : B} (hps : star p = p) (x : B) :
    star (evenGrade p x) = evenGrade p (star x) := by
  simp only [evenGrade, star_add, star_mul, star_sub, star_one, hps, mul_assoc]

/-- Star exchanges the two off-diagonal corners, preserving their sum. -/
theorem star_oddGrade {p : B} (hps : star p = p) (x : B) :
    star (oddGrade p x) = oddGrade p (star x) := by
  simp only [oddGrade, star_add, star_mul, star_sub, star_one, hps, mul_assoc]
  exact add_comm _ _

/-- The even affinity follows from the existing Peirce product law. -/
theorem evenGrade_affinity {p : B} (hp : p * p = p) (hps : star p = p)
    (q k : B) :
    evenGrade p (affinity q k) =
      affinity (evenGrade p q) (evenGrade p k) +
        affinity (oddGrade p q) (oddGrade p k) := by
  unfold affinity
  rw [evenGrade_mul hp, ← star_evenGrade hps, ← star_oddGrade hps]

/-- The odd affinity retains both ordered mixed-parity products. -/
theorem oddGrade_affinity {p : B} (hp : p * p = p) (hps : star p = p)
    (q k : B) :
    oddGrade p (affinity q k) =
      affinity (evenGrade p q) (oddGrade p k) +
        affinity (oddGrade p q) (evenGrade p k) := by
  unfold affinity
  rw [oddGrade_mul hp, ← star_oddGrade hps, ← star_evenGrade hps]

/-- Insert an actual form element between the two operators. -/
def twistedAffinity (j q k : B) : B := q * j * star k

theorem twistedAffinity_star (j q k : B) :
    star (twistedAffinity j q k) = twistedAffinity (star j) k q := by
  simp only [twistedAffinity, star_mul, star_star, mul_assoc]

/-- A skew-adjoint form makes swapping inputs skew-adjoint as well. -/
theorem twistedAffinity_star_of_skew {j : B} (hj : star j = -j) (q k : B) :
    star (twistedAffinity j q k) = -twistedAffinity j k q := by
  simp only [twistedAffinity, star_mul, star_star, hj, mul_neg, neg_mul, mul_assoc]

/-- Right-factor covariance changes the form by its ordered congruence. -/
theorem twistedAffinity_right_mul (j q k u v : B) :
    twistedAffinity j (q * u) (k * v) =
      twistedAffinity (u * j * star v) q k := by
  simp only [twistedAffinity, star_mul, mul_assoc]

/-- Apply the exact form-preservation equation to the actual co-transformation. -/
theorem twistedAffinity_congruence (j q k u : B)
    (hu : star u * j * u = j) :
    twistedAffinity j (q * star u) (k * star u) = twistedAffinity j q k := by
  simpa only [star_star, hu] using
    twistedAffinity_right_mul j q k (star u) (star u)

end InfoGeometry.OperatorAlgebra.PeirceAffinity
