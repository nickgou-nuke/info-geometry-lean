/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceTraceGeometry

/-!
# Directed Peirce corners and chiral square geometry

The existing directed corners are square-zero subspaces of the full matrix
algebra. Their sum need not be square-zero. For a Hermitian input and a star
projection, its square is exactly the Gram matrix of the native commutator.
The resulting positivity is semidefinite, with a faithful commutation criterion.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceChiralGeometry

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.IdempotentCartan
open MatrixOperatorIdentities MatrixTraceGeometry PeirceTraceGeometry
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The forward corner has weight one for the inner action of the idempotent. -/
theorem lie_component10 {p : Matrix n n ℂ} (hp : IsIdempotentElem p)
    (A : Matrix n n ℂ) : ⁅p, component10 p A⁆ = component10 p A := by
  have hl : p * component10 p A = component10 p A :=
    peirceCorner_absorb_left hp.eq
  have hr : component10 p A * p = 0 := by
    change p * A * (1 - p) * p = 0
    rw [mul_assoc, sub_mul, one_mul, hp.eq, sub_self, mul_zero]
  rw [Ring.lie_def, hl, hr, sub_zero]

/-- The reverse corner has weight minus one. -/
theorem lie_component01 {p : Matrix n n ℂ} (hp : IsIdempotentElem p)
    (A : Matrix n n ℂ) : ⁅p, component01 p A⁆ = -component01 p A := by
  have hl : p * component01 p A = 0 := by
    change p * ((1 - p) * A * p) = 0
    rw [← mul_assoc, ← mul_assoc, mul_sub, mul_one, hp.eq, sub_self,
      zero_mul, zero_mul]
  have hr : component01 p A * p = component01 p A :=
    peirceCorner_absorb_right hp.eq
  rw [Ring.lie_def, hl, hr, zero_sub]

theorem trace_component10 {p : Matrix n n ℂ} (hp : IsIdempotentElem p)
    (A : Matrix n n ℂ) : trace (component10 p A) = 0 := by
  rw [← lie_component10 hp A]
  exact trace_lie_zero p _

theorem trace_component01 {p : Matrix n n ℂ} (hp : IsIdempotentElem p)
    (A : Matrix n n ℂ) : trace (component01 p A) = 0 := by
  have h := trace_lie_zero p (component01 p A)
  rw [lie_component01 hp, trace_neg, neg_eq_zero] at h
  exact h

/-- Isotropy here is for the bilinear trace pairing, without an adjoint. -/
theorem trace_component10_mul_component10 {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    trace (component10 p A * component10 p B) = 0 := by
  rw [peirce10_mul_peirce10_eq_zero p hp.eq (component10_mem p A)
    (component10_mem p B), trace_zero]

theorem trace_component01_mul_component01 {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    trace (component01 p A * component01 p B) = 0 := by
  rw [peirce01_mul_peirce01_eq_zero p hp.eq (component01_mem p A)
    (component01_mem p B), trace_zero]

/-- The adjoint exchanges the two directed corners. -/
theorem star_component10 {p : Matrix n n ℂ} (hp : IsSelfAdjoint p)
    (A : Matrix n n ℂ) : star (component10 p A) = component01 p (star A) := by
  simp only [component10, component01, complementIdempotent, star_mul,
    star_sub, star_one, hp.star_eq, mul_assoc]

theorem star_component01 {p : Matrix n n ℂ} (hp : IsSelfAdjoint p)
    (A : Matrix n n ℂ) : star (component01 p A) = component10 p (star A) := by
  simp only [component10, component01, complementIdempotent, star_mul,
    star_sub, star_one, hp.star_eq, mul_assoc]

/-- The square contains precisely the two cross products. -/
theorem odd_square_eq_cross_products {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    oddPart p A * oddPart p A =
      component10 p A * component01 p A + component01 p A * component10 p A := by
  rcases corners_square_zero hp.eq A with ⟨hForward, hReverse⟩
  simp only [oddPart, add_mul, mul_add, hForward, hReverse, zero_add, add_zero]
  exact add_comm _ _

/-- Multiplication of odd operators returns to the even algebra. -/
theorem commute_odd_square {p : Matrix n n ℂ} (hp : IsIdempotentElem p)
    (A : Matrix n n ℂ) : Commute p (oddPart p A * oddPart p A) := by
  apply (odd_zero_iff_commute hp.eq _).mp
  rw [(multiplication_rules hp.eq _ _).2,
    (projection_laws hp.eq A).2.1, zero_mul, mul_zero, add_zero]

/-- The sign reversal is purely algebraic and needs no star hypotheses. -/
theorem odd_square_eq_neg_lie_square {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    oddPart p A * oddPart p A = -(⁅p, A⁆ * ⁅p, A⁆) := by
  have hJ : ⁅p, A⁆ * ⁅p, A⁆ = -(oddPart p A * oddPart p A) := by
    change (p * A - A * p) * (p * A - A * p) = _
    rw [← reflection_mul_odd hp.eq A]
    calc
      _ = (reflection p * oddPart p A * reflection p) * oddPart p A := by
        simp only [mul_assoc]
      _ = -(oddPart p A * oddPart p A) := by
        rw [(conjugation_on_parts hp.eq A).2, neg_mul]
  rw [hJ, neg_neg]

theorem oddPart_isSelfAdjoint {p A : Matrix n n ℂ}
    (hp : IsSelfAdjoint p) (hA : IsSelfAdjoint A) : IsSelfAdjoint (oddPart p A) := by
  change star (oddPart p A) = oddPart p A
  rw [star_oddPart hp, hA.star_eq]

/-- Exact equality to an operator Gram matrix, before taking any trace. -/
theorem odd_square_eq_lie_gram {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) (hA : IsSelfAdjoint A) :
    oddPart p A * oddPart p A = star ⁅p, A⁆ * ⁅p, A⁆ := by
  rw [star_lie_of_isSelfAdjoint hp.isSelfAdjoint hA, neg_mul]
  exact odd_square_eq_neg_lie_square hp.isIdempotentElem A

theorem odd_square_posSemidef {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) (hA : IsSelfAdjoint A) :
    (oddPart p A * oddPart p A).PosSemidef := by
  rw [odd_square_eq_lie_gram hp hA]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem neg_lie_square_posSemidef {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) (hA : IsSelfAdjoint A) :
    (-(⁅p, A⁆ * ⁅p, A⁆)).PosSemidef := by
  rw [← odd_square_eq_neg_lie_square hp.isIdempotentElem]
  exact odd_square_posSemidef hp hA

/-- Vanishing is equivalent to commutation; nonzero is not automatic. -/
theorem odd_square_eq_zero_iff_commute {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) (hA : IsSelfAdjoint A) :
    oddPart p A * oddPart p A = 0 ↔ Commute p A := by
  rw [odd_square_eq_lie_gram hp hA]
  change (⁅p, A⁆)ᴴ * ⁅p, A⁆ = 0 ↔ _
  rw [Matrix.conjTranspose_mul_self_eq_zero]
  change p * A - A * p = 0 ↔ p * A = A * p
  exact sub_eq_zero

theorem trace_odd_square_eq_zero_iff_commute {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) (hA : IsSelfAdjoint A) :
    trace (oddPart p A * oddPart p A) = 0 ↔ Commute p A := by
  rw [odd_square_eq_lie_gram hp hA]
  change trace ((⁅p, A⁆)ᴴ * ⁅p, A⁆) = 0 ↔ _
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff]
  change p * A - A * p = 0 ↔ p * A = A * p
  exact sub_eq_zero

/-- Over ℂ, the reflection anticommutation law exactly characterizes the odd part. -/
theorem oddPart_eq_self_iff_reflection_anticommute {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    oddPart p A = A ↔ reflection p * A + A * reflection p = 0 := by
  rw [oddPart_eq_self_iff_tangent hp]
  have h : reflection p * A + A * reflection p =
      (2 : ℂ) • (p * A + A * p - A) := by
    simp only [reflection, two_smul]
    noncomm_ring
  rw [h, smul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or, sub_eq_zero]

end InfoGeometry.OperatorAlgebra.PeirceChiralGeometry
