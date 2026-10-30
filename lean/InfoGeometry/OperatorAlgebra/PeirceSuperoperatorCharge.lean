/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceAdjointCycle
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Quintic annihilation of the Peirce superoperator charge

A tripotent in any associative ring induces a commutator satisfying
D⁵ - 5D³ + 4D = 0. Applying this to the existing integer-linear adjoint of
an idempotent proves the identity on every integer-linear endomorphism.
No division, minimal-polynomial claim, or identification with a TKK algebra
is required. The base adjoint tripotency is owned by `PeirceAdjointCycle`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperatorCharge

open PeirceSpine

variable {B : Type*} [Ring B]

/-- The quintic holds on every element, not only five chosen test operators. -/
theorem commutator_quintic_of_tripotent {e : B} (he : e * e * e = e) (x : B) :
    (comm e)^[5] x - (5 : ℤ) • ((comm e)^[3] x) + (4 : ℤ) • comm e x = 0 := by
  have he' : e * (e * e) = e := by simpa only [mul_assoc] using he
  have hprefix (z : B) : e * (e * (e * z)) = e * z := by
    simpa only [mul_assoc] using congrArg (fun a => a * z) he
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PeirceSpine.comm,
    mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, neg_neg,
    mul_assoc, he', hprefix]
  abel

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The adjoint charge on the full endomorphism ring satisfies the quintic.
Multiplication of endomorphisms is composition. -/
theorem peirce_superoperator_quintic {p : B} (hp : IsIdempotentElem p)
    (K : Module.End ℤ B) :
    let D := LieAlgebra.ad ℤ B p
    (comm D)^[5] K - (5 : ℤ) • ((comm D)^[3] K) + (4 : ℤ) • comm D K = 0 := by
  dsimp
  apply commutator_quintic_of_tripotent
  simpa only [pow_succ, pow_zero, mul_one, one_mul] using
    InfoGeometry.Core.PeirceAdjointCycle.ad_cube_eq_ad hp


section CornerCharges
variable {p : B} (hp : p * p = p) (a c x : B)
include hp

theorem upper_sandwich_charge :
    comm p (conePlus p a * x * conePlus p a) -
      conePlus p a * comm p x * conePlus p a =
      (2 : ℤ) • (conePlus p a * x * conePlus p a) := by
  peirce_nf hp

theorem lower_sandwich_charge :
    comm p (coneMinus p c * x * coneMinus p c) -
      coneMinus p c * comm p x * coneMinus p c =
      -((2 : ℤ) • (coneMinus p c * x * coneMinus p c)) := by
  peirce_nf hp

theorem upper_inner_charge :
    comm p (comm (conePlus p a) x) - comm (conePlus p a) (comm p x) =
      comm (conePlus p a) x := by
  peirce_nf hp

theorem lower_inner_charge :
    comm p (comm (coneMinus p c) x) - comm (coneMinus p c) (comm p x) =
      -comm (coneMinus p c) x := by
  peirce_nf hp

theorem cross_sandwich_charge :
    comm p (conePlus p a * x * coneMinus p c + coneMinus p c * x * conePlus p a) -
      (conePlus p a * comm p x * coneMinus p c +
        coneMinus p c * comm p x * conePlus p a) = 0 := by
  peirce_nf hp

end CornerCharges

end InfoGeometry.OperatorAlgebra.PeirceSuperoperatorCharge
