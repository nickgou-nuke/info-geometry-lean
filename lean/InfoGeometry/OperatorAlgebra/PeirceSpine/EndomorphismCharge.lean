/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge
import InfoGeometry.Core.PeirceAdjointCycle

/-!
# The charge annihilator on all integer-linear endomorphisms

The cubic relation for ad P implies a fifth-degree relation for its commutator
on the full endomorphism ring. No eigenbasis, characteristic restriction, or
commutation of the tested endomorphism with ad P is assumed.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {B : Type*} [Ring B]

/-- Universal associative-ring identity for a tripotent acting by commutators. -/
theorem tripotent_comm_fifth {q : B} (hq : q * q * q = q) (x : B) :
    comm q (comm q (comm q (comm q (comm q x)))) -
      (5 : ℤ) • comm q (comm q (comm q x)) + (4 : ℤ) • comm q x = 0 := by
  have hq' : q * (q * q) = q := by simpa only [mul_assoc] using hq
  have hn (y : B) : q * (q * (q * y)) = q * y := by
    rw [← mul_assoc q q (q * y), ← mul_assoc, hq]
  simp only [comm, mul_sub, sub_mul, mul_assoc, hq', hn]
  abel

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The full charge operator, bundled as a native integer-linear endomorphism. -/
def endomorphismCharge (P : B) : Module.End ℤ (Module.End ℤ B) :=
  LieAlgebra.ad ℤ (Module.End ℤ B) (LieAlgebra.ad ℤ B P)

theorem endomorphismCharge_apply (P : B) (K : Module.End ℤ B) (X : B) :
    endomorphismCharge P K X = charge P K X := rfl

/-- The annihilator holds on every integer-linear endomorphism, not just sandwiches. -/
theorem endomorphismCharge_fifth {P : B} (hP : P * P = P)
    (K : Module.End ℤ B) :
    (endomorphismCharge P ^ 5) K - (5 : ℤ) • (endomorphismCharge P ^ 3) K +
      (4 : ℤ) • endomorphismCharge P K = 0 := by
  have hq : (LieAlgebra.ad ℤ B P) * (LieAlgebra.ad ℤ B P) *
      (LieAlgebra.ad ℤ B P) = LieAlgebra.ad ℤ B P := by
    simpa only [pow_succ, pow_zero, one_mul] using
      InfoGeometry.Core.PeirceAdjointCycle.ad_cube_eq_ad hP
  exact tripotent_comm_fifth hq K

/-- The bundled powers agree with the pointwise recursion used by the intake. -/
theorem endomorphismCharge_pow_apply (P : B) (K : Module.End ℤ B)
    (n : ℕ) (X : B) :
    (endomorphismCharge P ^ n) K X = chargeIter P K n X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change charge P ((endomorphismCharge P ^ n) K) X =
      charge P (chargeIter P K n) X
    simp only [charge, ih]

theorem chargeIter_fifth_of_linear {P : B} (hP : P * P = P)
    (K : Module.End ℤ B) (X : B) :
    chargeIter P K 5 X - (5 : ℤ) • chargeIter P K 3 X +
      (4 : ℤ) • chargeIter P K 1 X = 0 := by
  have h := congrArg (fun L : Module.End ℤ B => L X)
    (endomorphismCharge_fifth hP K)
  simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, endomorphismCharge_pow_apply, chargeIter,
    endomorphismCharge_apply] using h

end InfoGeometry.OperatorAlgebra.PeirceSpine
