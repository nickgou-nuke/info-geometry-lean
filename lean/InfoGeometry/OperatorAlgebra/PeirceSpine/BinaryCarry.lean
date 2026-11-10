/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import Mathlib.Algebra.Ring.Commute
import Mathlib.GroupTheory.OrderOfElement

/-!
# Normalized Peirce operators and binary-carry square roots

The existing Peirce corners supply an internal square-negative element when
`genPhi` squares to one. A second, commuting Peirce bit then takes its square
root using only integral ring operations. The ambient ring is not assumed
commutative. Exact order eight additionally requires `-1 ≠ 1`.

The inverse is algebraic: no adjoint or metric is implicit. Conjugation by a
first-bit grading alone does not generally invert the carry; its composite
with the second-bit flip supplies the inverse-conjugation formula. No dimension, Clifford equivalence or braid relation is
asserted by these identities.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

section Normalized

variable {P : B} (hP : P * P = P) (A C : B)
include hP

/-- The normalized symmetric bridge has unit Jordan return. -/
theorem genV_eq_one_of_genPhi_sq
    (hPhi : genPhi P A C * genPhi P A C = 1) : genV P A C = 1 := by
  exact (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1.symm.trans hPhi

/-- Normalization turns the oriented bridge into an internal square-negative unit. -/
theorem genJ_sq_of_genPhi_sq
    (hPhi : genPhi P A C * genPhi P A C = 1) :
    genJ P A C * genJ P A C = -1 := by
  rw [(archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.2.1,
    genV_eq_one_of_genPhi_sq hP A C hPhi]

/-- Left grading preserves the order of the two Peirce corners. -/
theorem invS_mul_genPhi : invS P * genPhi P A C = genJ P A C := by
  peirce_nf hP

/-- Right grading has the opposite sign. -/
theorem genPhi_mul_invS : genPhi P A C * invS P = -genJ P A C := by
  peirce_nf hP

theorem invS_mul_genJ : invS P * genJ P A C = genPhi P A C := by
  peirce_nf hP

theorem genJ_mul_invS : genJ P A C * invS P = -genPhi P A C := by
  peirce_nf hP

/-- Conjugating the oriented bridge by the grading reverses its sign. -/
theorem invS_conjugates_genJ :
    invS P * genJ P A C * invS P = -genJ P A C := by
  rw [invS_mul_genJ hP, genPhi_mul_invS hP]

/-- The normalized symmetric bridge also reverses the oriented bridge. -/
theorem genPhi_conjugates_genJ
    (hPhi : genPhi P A C * genPhi P A C = 1) :
    genPhi P A C * genJ P A C * genPhi P A C = -genJ P A C := by
  calc
    genPhi P A C * genJ P A C * genPhi P A C =
        genPhi P A C * (invS P * genPhi P A C) * genPhi P A C := by
          rw [invS_mul_genPhi hP]
    _ = (genPhi P A C * invS P) * (genPhi P A C * genPhi P A C) := by
          simp only [mul_assoc]
    _ = -genJ P A C := by rw [genPhi_mul_invS hP, hPhi, mul_one]

/-- Normalization recovers the two ordered matrix-unit return products. -/
theorem normalized_corner_returns
    (hPhi : genPhi P A C * genPhi P A C = 1) :
    conePlus P A * coneMinus P C = P ∧
      coneMinus P C * conePlus P A = 1 - P := by
  have hV := genV_eq_one_of_genPhi_sq hP A C hPhi
  have hleft : P * genV P A C = conePlus P A * coneMinus P C := by peirce_nf hP
  have hright : (1 - P) * genV P A C = coneMinus P C * conePlus P A := by
    peirce_nf hP
  constructor
  · rw [← hleft, hV, mul_one]
  · rw [← hright, hV, mul_one]

end Normalized

/-- Flip the second bit, applying `a` on its complementary output corner. -/
def binaryCarry (p f a : B) : B := p * f + (1 - p) * a * f

/-- The inverse expression when the carried element squares to minus one. -/
def binaryCarryInverse (p f a : B) : B := (1 - p) * f - p * a * f

/-- An element commuting with the three inputs also commutes with the carry.
This transfers a local centralizer condition without making the ring commutative. -/
theorem binaryCarry_commute {p f a x : B}
    (hpx : Commute p x) (hfx : Commute f x) (hax : Commute a x) :
    Commute (binaryCarry p f a) x := by
  exact (hpx.mul_left hfx).add_left
    ((((Commute.one_left x).sub_left hpx).mul_left hax).mul_left hfx)

section Carry

variable {p f a : B}
variable (hp : p * p = p) (hf : f * f = 1)
variable (hswap : f * p = (1 - p) * f)
variable (hap : Commute a p) (haf : Commute a f)
include hp hf hswap hap haf

/-- The binary carry squares to any element commuting with the second bit. -/
theorem binaryCarry_sq : binaryCarry p f a * binaryCarry p f a = a := by
  have hpp (z : B) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  have hff (z : B) : f * (f * z) = z := by rw [← mul_assoc, hf, one_mul]
  have hfp : f * p = f - p * f := by simpa only [sub_mul, one_mul] using hswap
  have hfp' (z : B) : f * (p * z) = f * z - p * (f * z) := by
    rw [← mul_assoc, hfp, sub_mul, mul_assoc]
  have hap' (z : B) : a * (p * z) = p * (a * z) := hap.left_comm z
  have hfa' (z : B) : f * (a * z) = a * (f * z) := haf.symm.left_comm z
  unfold binaryCarry
  noncomm_ring [hfp, hfp', hap.eq, hap', haf.eq.symm, hfa', hp, hpp, hf, hff]

/-- Carrying an internal square-negative element yields a fourth power of `-1`. -/
theorem binaryCarry_pow_four (ha : a * a = -1) : binaryCarry p f a ^ 4 = -1 := by
  calc
    binaryCarry p f a ^ 4 =
        (binaryCarry p f a * binaryCarry p f a) *
          (binaryCarry p f a * binaryCarry p f a) := by noncomm_ring
    _ = -1 := by rw [binaryCarry_sq hp hf hswap hap haf, ha]

/-- The eighth power is one in every characteristic. -/
theorem binaryCarry_pow_eight (ha : a * a = -1) : binaryCarry p f a ^ 8 = 1 := by
  calc
    binaryCarry p f a ^ 8 = (binaryCarry p f a ^ 4) ^ 2 := by
      rw [← pow_mul]
    _ = 1 := by rw [binaryCarry_pow_four hp hf hswap hap haf ha]; simp

/-- Exact order, with the characteristic-degeneracy hypothesis exposed. -/
theorem binaryCarry_orderOf_eight (ha : a * a = -1) (hneg : (-1 : B) ≠ 1) :
    orderOf (binaryCarry p f a) = 8 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 2)
  · simpa only [show 2 ^ 2 = 4 from rfl,
      binaryCarry_pow_four hp hf hswap hap haf ha] using hneg
  · simpa only [show 2 ^ (2 + 1) = 8 from rfl] using
      binaryCarry_pow_eight hp hf hswap hap haf ha

omit hp hf hswap haf in
/-- The explicit inverse is minus the carried element times the carry. -/
theorem binaryCarryInverse_eq_neg_mul (ha : a * a = -1) :
    binaryCarryInverse p f a = -a * binaryCarry p f a := by
  have haa (z : B) : a * (a * z) = -z := by rw [← mul_assoc, ha, neg_one_mul]
  have hap' (z : B) : a * (p * z) = p * (a * z) := hap.left_comm z
  unfold binaryCarryInverse binaryCarry
  noncomm_ring [hap.eq, hap', ha, haa]

/-- Inverse polynomial, without using a division operation in the ambient ring. -/
theorem binaryCarryInverse_eq_neg_cube (ha : a * a = -1) :
    binaryCarryInverse p f a = -(binaryCarry p f a ^ 3) := by
  calc
    binaryCarryInverse p f a = -a * binaryCarry p f a :=
      binaryCarryInverse_eq_neg_mul hap ha
    _ = -((binaryCarry p f a * binaryCarry p f a) * binaryCarry p f a) := by
      rw [binaryCarry_sq hp hf hswap hap haf, neg_mul]
    _ = -(binaryCarry p f a ^ 3) := by noncomm_ring

/-- Both ordered inverse products are proved explicitly. -/
theorem binaryCarry_mul_inverse (ha : a * a = -1) :
    binaryCarry p f a * binaryCarryInverse p f a = 1 := by
  rw [binaryCarryInverse_eq_neg_cube hp hf hswap hap haf ha, mul_neg,
    ← pow_succ', binaryCarry_pow_four hp hf hswap hap haf ha]
  exact neg_neg 1

theorem binaryCarry_inverse_mul (ha : a * a = -1) :
    binaryCarryInverse p f a * binaryCarry p f a = 1 := by
  rw [binaryCarryInverse_eq_neg_cube hp hf hswap hap haf ha, neg_mul,
    ← pow_succ, binaryCarry_pow_four hp hf hswap hap haf ha]
  exact neg_neg 1

/-- Native unit carrying the constructed value and its two-sided inverse. -/
def binaryCarryUnit (ha : a * a = -1) : Bˣ where
  val := binaryCarry p f a
  inv := binaryCarryInverse p f a
  val_inv := binaryCarry_mul_inverse hp hf hswap hap haf ha
  inv_val := binaryCarry_inverse_mul hp hf hswap hap haf ha

end Carry

section Reflection

variable {p f a s : B}

/-- Conjugation by an involution is multiplicative, with the factors ordered. -/
private theorem involution_conjugate_mul (hs : s * s = 1) (x y : B) :
    s * (x * y) * s = (s * x * s) * (s * y * s) := by
  calc
    s * (x * y) * s = s * x * (s * s) * y * s := by rw [hs]; simp only [mul_one, mul_assoc]
    _ = (s * x * s) * (s * y * s) := by simp only [mul_assoc]

/-- The composite of the commuting first grading and second flip is an involution. -/
theorem carryReflection_sq (hs : s * s = 1) (hf : f * f = 1)
    (hsf : Commute s f) : (s * f) * (s * f) = 1 := by
  calc
    (s * f) * (s * f) = (s * s) * (f * f) := by
      rw [mul_assoc, ← hsf.left_comm, ← mul_assoc]
    _ = 1 := by rw [hs, hf, one_mul]

/-- The composite grading and flip conjugates the carry to its explicit inverse expression. -/
theorem carryReflection_conjugates (hs : s * s = 1) (hf : f * f = 1)
    (hswap : f * p = (1 - p) * f)
    (hsp : Commute s p) (hsf : Commute s f)
    (hsa : s * a = -(a * s)) (haf : Commute a f) :
    (s * f) * binaryCarry p f a * (s * f) = binaryCarryInverse p f a := by
  have hspc : s * p * s = p := by
    rw [hsp.eq, mul_assoc, hs, mul_one]
  have hsfc : s * f * s = f := by
    rw [hsf.eq, mul_assoc, hs, mul_one]
  have hsac : s * a * s = -a := by
    rw [hsa, neg_mul, mul_assoc, hs, mul_one]
  have hfpc : f * p * f = 1 - p := by
    rw [hswap, mul_assoc, hf, mul_one]
  have hfac : f * a * f = a := by
    rw [haf.eq.symm, mul_assoc, hf, mul_one]
  have hffc : f * f * f = f := by rw [hf, one_mul]
  have hsc : s * (1 - p) * s = 1 - p := by
    calc
      s * (1 - p) * s = s * s - s * p * s := by noncomm_ring
      _ = 1 - p := by rw [hs, hspc]
  have hfc : f * (1 - p) * f = p := by
    calc
      f * (1 - p) * f = f * f - f * p * f := by noncomm_ring
      _ = p := by rw [hf, hfpc]; abel
  have hsroot : s * binaryCarry p f a * s = p * f - (1 - p) * a * f := by
    unfold binaryCarry
    simp only [mul_add, add_mul, involution_conjugate_mul hs,
      hspc, hsfc, hsc, hsac]
    noncomm_ring
  calc
    (s * f) * binaryCarry p f a * (s * f) =
        f * (s * binaryCarry p f a * s) * f := by
          noncomm_ring [hsf.eq, hsf.left_comm]
    _ = f * (p * f - (1 - p) * a * f) * f := by rw [hsroot]
    _ = (f * p * f) * (f * f * f) -
        ((f * (1 - p) * f) * (f * a * f)) * (f * f * f) := by
          rw [mul_sub, sub_mul]
          simp only [involution_conjugate_mul hf]
    _ = (1 - p) * f - p * a * f := by rw [hfpc, hffc, hfc, hfac]
    _ = binaryCarryInverse p f a := rfl

end Reflection

end InfoGeometry.OperatorAlgebra.PeirceSpine
