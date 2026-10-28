/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeircePairGeometry

/-!
# Gram geometry of adjoint opposite Peirce corners

For a star projection, pairing the forward corner of an arbitrary matrix with
the reverse corner of its adjoint gives a self-adjoint odd matrix. Its square
is the sum of two positive-semidefinite Gram matrices. Faithful vanishing and
the exact vector kernel distinguish this conclusion from positive definiteness.
-/

namespace InfoGeometry.OperatorAlgebra.PeircePairPositivity

open Matrix InfoGeometry.Core.PeirceDecomposition
open PeirceChiralGeometry PeircePairGeometry
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Adjoint-paired directed corners have a self-adjoint sum. -/
theorem pair_sum_isSelfAdjoint {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    IsSelfAdjoint (component10 p A + component01 p (star A)) := by
  rw [← star_component10 hp.isSelfAdjoint A]
  exact IsSelfAdjoint.add_star_self _

/-- The mixed Jordan expression is exactly a sum of operator Gram matrices. -/
theorem pair_jordan_eq_gram_sum {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    component10 p A * component01 p (star A) +
        component01 p (star A) * component10 p A =
      component10 p A * star (component10 p A) +
        star (component10 p A) * component10 p A := by
  rw [← star_component10 hp.isSelfAdjoint A]

/-- The first compression is the Gram matrix on the range of the corner. -/
theorem component11_adjoint_pair_eq_gram {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) :
    component11 p (component10 p A * component01 p (star A) +
      component01 p (star A) * component10 p A) =
      component10 p A * star (component10 p A) := by
  rw [component11_pair_jordan hp.isIdempotentElem A (star A),
    ← star_component10 hp.isSelfAdjoint A]

/-- The complementary compression is the Gram matrix on the domain of the corner. -/
theorem component00_adjoint_pair_eq_gram {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) :
    component00 p (component10 p A * component01 p (star A) +
      component01 p (star A) * component10 p A) =
      star (component10 p A) * component10 p A := by
  rw [component00_pair_jordan hp.isIdempotentElem A (star A),
    ← star_component10 hp.isSelfAdjoint A]

theorem component11_adjoint_pair_posSemidef {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) :
    (component11 p (component10 p A * component01 p (star A) +
      component01 p (star A) * component10 p A)).PosSemidef := by
  rw [component11_adjoint_pair_eq_gram hp A]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem component00_adjoint_pair_posSemidef {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) :
    (component00 p (component10 p A * component01 p (star A) +
      component01 p (star A) * component10 p A)).PosSemidef := by
  rw [component00_adjoint_pair_eq_gram hp A]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Positivity follows from the adjoint pairing, with no assumption on commutation. -/
theorem adjoint_pair_posSemidef {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    (component10 p A * component01 p (star A) +
      component01 p (star A) * component10 p A).PosSemidef := by
  rw [pair_jordan_eq_gram_sum hp A]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).add
    (Matrix.posSemidef_conjTranspose_mul_self _)

theorem adjoint_pair_isSelfAdjoint {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    IsSelfAdjoint (component10 p A * component01 p (star A) +
      component01 p (star A) * component10 p A) :=
  (adjoint_pair_posSemidef hp A).isHermitian.isSelfAdjoint

/-- Faithfulness detects the directed corner, not commutation with the arbitrary input. -/
theorem adjoint_pair_eq_zero_iff {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    component10 p A * component01 p (star A) +
        component01 p (star A) * component10 p A = 0 ↔
      component10 p A = 0 := by
  rw [pair_jordan_eq_zero_iff_products hp.isIdempotentElem A (star A),
    ← star_component10 hp.isSelfAdjoint A]
  constructor
  · intro h
    exact Matrix.self_mul_conjTranspose_eq_zero.mp h.1
  · intro h
    simp only [h, star_zero, zero_mul, and_self]

/-- The cyclic trace is faithful on the adjoint-paired Jordan expression. -/
theorem trace_adjoint_pair_eq_zero_iff {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) :
    trace (component10 p A * component01 p (star A) +
        component01 p (star A) * component10 p A) = 0 ↔
      component10 p A = 0 := by
  rw [trace_pair_jordan p A (star A),
    ← star_component10 hp.isSelfAdjoint A]
  change (2 : ℂ) * (component10 p A * (component10 p A)ᴴ).trace = 0 ↔ _
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff]

/-- The opposite-corner Lie bracket vanishes precisely with the forward corner. -/
theorem adjoint_pair_lie_eq_zero_iff {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) :
    ⁅component10 p A, component01 p (star A)⁆ = 0 ↔ component10 p A = 0 := by
  rw [← pair_jordan_eq_zero_iff_lie hp.isIdempotentElem A (star A)]
  exact adjoint_pair_eq_zero_iff hp A

/-- This commutator is Hermitian: its two inputs are an adjoint pair. -/
theorem adjoint_pair_lie_isSelfAdjoint {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) :
    IsSelfAdjoint ⁅component10 p A, component01 p (star A)⁆ := by
  rw [← star_component10 hp.isSelfAdjoint A]
  change star (component10 p A * star (component10 p A) -
      star (component10 p A) * component10 p A) = _
  simp only [star_sub, star_mul, star_star, Ring.lie_def]

/-- The nullspace is exactly the intersection of the two directed kernels. -/
theorem adjoint_pair_mulVec_eq_zero_iff {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) (v : n → ℂ) :
    (component10 p A * component01 p (star A) +
        component01 p (star A) * component10 p A) *ᵥ v = 0 ↔
      component10 p A *ᵥ v = 0 ∧ star (component10 p A) *ᵥ v = 0 := by
  have hself := pair_sum_isSelfAdjoint hp A
  have hgram :
      component10 p A * component01 p (star A) +
          component01 p (star A) * component10 p A =
        star (component10 p A + component01 p (star A)) *
          (component10 p A + component01 p (star A)) := by
    rw [hself.star_eq, pair_square hp.isIdempotentElem A (star A)]
  rw [hgram]
  change (((component10 p A + component01 p (star A))ᴴ *
    (component10 p A + component01 p (star A))) *ᵥ v = 0) ↔ _
  rw [Matrix.conjTranspose_mul_self_mulVec_eq_zero,
    star_component10 hp.isSelfAdjoint A]
  exact pair_sum_mulVec_eq_zero_iff hp.isIdempotentElem A (star A) v

/-- Positive definiteness requires injectivity of the odd sum, not mere nonzeroness. -/
theorem adjoint_pair_posDef_iff_injective {p : Matrix n n ℂ}
    (hp : IsStarProjection p) (A : Matrix n n ℂ) :
    (component10 p A * component01 p (star A) +
        component01 p (star A) * component10 p A).PosDef ↔
      Function.Injective (component10 p A + component01 p (star A)).mulVec := by
  constructor
  · intro h x y hxy
    apply Matrix.mulVec_injective_of_isUnit h.isUnit
    simpa only [← pair_square hp.isIdempotentElem A (star A),
      ← Matrix.mulVec_mulVec] using
      congrArg (fun z => (component10 p A + component01 p (star A)) *ᵥ z) hxy
  · intro h
    have hpos := Matrix.PosDef.conjTranspose_mul_self
      (component10 p A + component01 p (star A)) h
    change (star (component10 p A + component01 p (star A)) *
      (component10 p A + component01 p (star A))).PosDef at hpos
    rwa [(pair_sum_isSelfAdjoint hp A).star_eq,
      pair_square hp.isIdempotentElem A (star A)] at hpos

end InfoGeometry.OperatorAlgebra.PeircePairPositivity
