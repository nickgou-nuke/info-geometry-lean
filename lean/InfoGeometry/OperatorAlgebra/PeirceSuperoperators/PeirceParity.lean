/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Core.PeirceGrading
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

/-!
# The actual Peirce parity as an algebra equivalence

The existing reflection ring equivalence preserves the scalar algebra map.
Its algebra-equivalence upgrade acts with the required signs on the existing
Peirce submodules, including over rings where doubling is not injective.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open InfoGeometry.Core

section PureRing

variable {A : Type*} [Ring A]

/-- Pure ring-equivalence Peirce parity over any noncommutative ring `A`
(requiring no scalar `CommRing` or `Algebra`). -/
def ringParityEquiv (p : A) (hp : IsIdempotentElem p) : A ≃+* A :=
  IdempotentCartan.reflectionConj p hp.eq

@[simp] theorem ringParityEquiv_apply (p : A) (hp : IsIdempotentElem p) (x : A) :
    ringParityEquiv p hp x =
      PeirceGrading.reflection p * x * PeirceGrading.reflection p := by
  change IdempotentCartan.reflection p * x * IdempotentCartan.reflection p = _
  simp only [IdempotentCartan.reflection, PeirceGrading.reflection, two_nsmul, two_mul]

theorem ringParityEquiv_involutive (p : A) (hp : IsIdempotentElem p) :
    Function.Involutive (ringParityEquiv p hp) := by
  intro x
  simp only [ringParityEquiv_apply]
  calc
    _ = (PeirceGrading.reflection p * PeirceGrading.reflection p) * x *
        (PeirceGrading.reflection p * PeirceGrading.reflection p) := by noncomm_ring
    _ = x := by rw [PeirceGrading.reflection_sq hp]; simp

theorem ringParityEquiv_of_even {p x : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (PeirceGrading.even p)) :
    ringParityEquiv p hp x = x := by
  rw [ringParityEquiv_apply, (PeirceGrading.even_commutes_reflection hp hx).eq,
    mul_assoc, PeirceGrading.reflection_sq hp, mul_one]

theorem ringParityEquiv_of_odd {p x : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (PeirceGrading.odd p)) :
    ringParityEquiv p hp x = -x := by
  rw [ringParityEquiv_apply,
    eq_neg_of_add_eq_zero_left (PeirceGrading.odd_anticommutes_reflection hp hx),
    neg_mul, mul_assoc, PeirceGrading.reflection_sq hp, mul_one]

theorem ringParityEquiv_star [StarRing A] (p : A) (hp : IsIdempotentElem p)
    (hps : IsSelfAdjoint p) (x : A) :
    ringParityEquiv p hp (star x) = star (ringParityEquiv p hp x) := by
  simp only [ringParityEquiv_apply, star_mul,
    (PeirceGrading.reflection_star hps).star_eq, mul_assoc]

end PureRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Scalar-linear upgrade of the existing reflection conjugation equivalence. -/
def parityEquiv (p : A) (hp : IsIdempotentElem p) : A ≃ₐ[R] A :=
  AlgEquiv.ofRingEquiv (f := IdempotentCartan.reflectionConj p hp.eq) fun r => by
    change IdempotentCartan.reflection p * algebraMap R A r *
      IdempotentCartan.reflection p = algebraMap R A r
    rw [← Algebra.commutes r (IdempotentCartan.reflection p), mul_assoc,
      IdempotentCartan.reflection_sq hp.eq, mul_one]

@[simp] theorem parityEquiv_apply (p : A) (hp : IsIdempotentElem p) (x : A) :
    parityEquiv (R := R) p hp x =
      PeirceGrading.reflection p * x * PeirceGrading.reflection p := by
  change IdempotentCartan.reflection p * x * IdempotentCartan.reflection p = _
  simp only [IdempotentCartan.reflection, PeirceGrading.reflection, two_nsmul, two_mul]

theorem parityEquiv_involutive (p : A) (hp : IsIdempotentElem p) :
    Function.Involutive (parityEquiv (R := R) p hp) := by
  intro x
  simp only [parityEquiv_apply]
  calc
    _ = (PeirceGrading.reflection p * PeirceGrading.reflection p) * x *
        (PeirceGrading.reflection p * PeirceGrading.reflection p) := by noncomm_ring
    _ = x := by rw [PeirceGrading.reflection_sq hp]; simp

/-- The upgraded equivalence and the existing integral endomorphism have the same action. -/
theorem parityEquiv_eq_conjugation (p : A) (hp : IsIdempotentElem p) (x : A) :
    parityEquiv (R := R) p hp x = PeirceGrading.conjugation p x := by
  rw [parityEquiv_apply, PeirceGrading.conjugation_apply]

theorem parityEquiv_of_even {p x : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (PeirceGrading.even p)) :
    parityEquiv (R := R) p hp x = x := by
  rw [parityEquiv_apply, (PeirceGrading.even_commutes_reflection hp hx).eq,
    mul_assoc, PeirceGrading.reflection_sq hp, mul_one]

theorem parityEquiv_of_odd {p x : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (PeirceGrading.odd p)) :
    parityEquiv (R := R) p hp x = -x := by
  rw [parityEquiv_apply,
    eq_neg_of_add_eq_zero_left (PeirceGrading.odd_anticommutes_reflection hp hx),
    neg_mul, mul_assoc, PeirceGrading.reflection_sq hp, mul_one]

/-- Self-adjoint support makes the actual parity star-compatible. -/
theorem parityEquiv_star [StarRing A] (p : A) (hp : IsIdempotentElem p)
    (hps : IsSelfAdjoint p) (x : A) :
    parityEquiv (R := R) p hp (star x) = star (parityEquiv (R := R) p hp x) := by
  simp only [parityEquiv_apply, star_mul,
    (PeirceGrading.reflection_star hps).star_eq, mul_assoc]

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
