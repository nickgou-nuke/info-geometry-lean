/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceCouplingGeometry
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Complex.Order

/-!
# Positive geometry of adjoint-paired Peirce corners

All operators are full complex matrices. A supported corner and its adjoint
form a Hermitian coupled operator whose square is the sum of the two native
Gram products. The exact common kernel determines positive definiteness;
nonzero coupling alone only gives a nonzero positive semidefinite operator.

The Gram positivity and Hermitian statements hold for arbitrary matrices.
The support hypotheses are used for the coupled-square identity and for
extracting the separate corner kernels and zero criteria.
-/

namespace InfoGeometry.Canonical.PeirceCouplingPositivity

open Matrix
open scoped ComplexOrder

open Core.PeirceDecomposition Core.PeirceCoupledCorners
open PeirceCouplingGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p u : Matrix n n ℂ}

/-- Taking the adjoint exchanges the existing directed Peirce sectors. -/
theorem adjoint_mem_peirce01 (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) : uᴴ ∈ peirce01 p := by
  simpa only [Matrix.star_eq_conjTranspose] using
    star_mem_peirce01 hp.isSelfAdjoint hu

omit [Fintype n] [DecidableEq n] in
/-- The adjoint-paired coupled matrix is Hermitian without a support assumption. -/
theorem coupled_isHermitian (u : Matrix n n ℂ) :
    (u + uᴴ).IsHermitian :=
  Matrix.isHermitian_add_transpose_self u

omit [DecidableEq n] in
/-- The bracket of a matrix with its adjoint is Hermitian. -/
theorem bracket_isHermitian (u : Matrix n n ℂ) :
    (⁅u, uᴴ⁆).IsHermitian := by
  change (u * uᴴ - uᴴ * u).IsHermitian
  exact (Matrix.isHermitian_mul_conjTranspose_self u).sub
    (Matrix.isHermitian_conjTranspose_mul_self u)

omit [DecidableEq n] in
/-- The two opposite Gram products have a positive semidefinite sum. -/
theorem gram_posSemidef (u : Matrix n n ℂ) :
    (u * uᴴ + uᴴ * u).PosSemidef :=
  (Matrix.posSemidef_self_mul_conjTranspose u).add
    (Matrix.posSemidef_conjTranspose_mul_self u)

omit [DecidableEq n] in
theorem gram_isHermitian (u : Matrix n n ℂ) :
    (u * uᴴ + uᴴ * u).IsHermitian :=
  (gram_posSemidef u).isHermitian

/-- Opposite support removes the two same-corner square terms. -/
theorem coupled_square_eq_gram (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    (u + uᴴ) ^ 2 = u * uᴴ + uᴴ * u :=
  coupled_square hp.isIdempotentElem hu (adjoint_mem_peirce01 hp hu)

theorem coupled_square_posSemidef (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) : ((u + uᴴ) ^ 2).PosSemidef := by
  rw [coupled_square_eq_gram hp hu]
  exact gram_posSemidef u

/-- The positive compressed bracket is the first corner Gram product. -/
theorem bracket_component11_posSemidef (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) : (component11 p ⁅u, uᴴ⁆).PosSemidef := by
  rw [component11_bracket hp.isIdempotentElem hu (adjoint_mem_peirce01 hp hu)]
  exact Matrix.posSemidef_self_mul_conjTranspose u

/-- The negative of the opposite bracket compression is the second Gram product. -/
theorem neg_bracket_component00_posSemidef (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) : (-component00 p ⁅u, uᴴ⁆).PosSemidef := by
  rw [component00_bracket hp.isIdempotentElem hu (adjoint_mem_peirce01 hp hu),
    neg_neg]
  exact Matrix.posSemidef_conjTranspose_mul_self u

/-- Compression and native Gram detection give the precise zero condition. -/
theorem gram_eq_zero_iff (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    u * uᴴ + uᴴ * u = 0 ↔ u = 0 := by
  rw [jordan_eq_zero_iff_products hp.isIdempotentElem hu
    (adjoint_mem_peirce01 hp hu)]
  simp only [Matrix.self_mul_conjTranspose_eq_zero,
    Matrix.conjTranspose_mul_self_eq_zero, and_self]

theorem coupled_square_eq_zero_iff (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    (u + uᴴ) ^ 2 = 0 ↔ u = 0 := by
  rw [coupled_square_eq_gram hp hu, gram_eq_zero_iff hp hu]

/-- The reflected bracket has the same exact zero condition. -/
theorem bracket_eq_zero_iff (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) : ⁅u, uᴴ⁆ = 0 ↔ u = 0 :=
  (jordan_eq_zero_iff_bracket_eq_zero hp.isIdempotentElem hu
    (adjoint_mem_peirce01 hp hu)).symm.trans (gram_eq_zero_iff hp hu)

omit [DecidableEq n] in
theorem gram_trace_nonneg (u : Matrix n n ℂ) :
    0 ≤ trace (u * uᴴ + uᴴ * u) :=
  (gram_posSemidef u).trace_nonneg

/-- Native trace detection for a positive semidefinite matrix detects the corner. -/
theorem gram_trace_eq_zero_iff (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    trace (u * uᴴ + uᴴ * u) = 0 ↔ u = 0 :=
  (gram_posSemidef u).trace_eq_zero_iff.trans (gram_eq_zero_iff hp hu)

/-- Strictly positive trace is equivalent to a nonzero supported corner. -/
theorem gram_trace_pos_iff (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    0 < trace (u * uᴴ + uᴴ * u) ↔ u ≠ 0 := by
  constructor
  · intro ht hu0
    exact ht.ne' ((gram_trace_eq_zero_iff hp hu).mpr hu0)
  · intro hu0
    apply lt_of_le_of_ne (gram_trace_nonneg u)
    intro ht
    exact hu0 ((gram_trace_eq_zero_iff hp hu).mp ht.symm)

/-- The positive coupled square has exactly the common zero modes of both corners. -/
theorem gram_kernel (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    LinearMap.ker (u * uᴴ + uᴴ * u).mulVecLin =
      LinearMap.ker u.mulVecLin ⊓ LinearMap.ker uᴴ.mulVecLin := by
  have hs : (u + uᴴ).conjTranspose = u + uᴴ := coupled_isHermitian u
  calc
    LinearMap.ker (u * uᴴ + uᴴ * u).mulVecLin =
        LinearMap.ker ((u + uᴴ) ^ 2).mulVecLin := by
      rw [coupled_square_eq_gram hp hu]
    _ = LinearMap.ker (u + uᴴ).mulVecLin := by
      simpa only [hs, pow_two] using
        Matrix.ker_mulVecLin_conjTranspose_mul_self (u + uᴴ)
    _ = LinearMap.ker u.mulVecLin ⊓ LinearMap.ker uᴴ.mulVecLin :=
      coupled_kernel hp.isIdempotentElem hu (adjoint_mem_peirce01 hp hu)

/-- The Hermitian bracket has the same common zero modes. -/
theorem bracket_kernel (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    LinearMap.ker (⁅u, uᴴ⁆).mulVecLin =
      LinearMap.ker u.mulVecLin ⊓ LinearMap.ker uᴴ.mulVecLin :=
  (jordan_kernel_eq_bracket_kernel hp.isIdempotentElem hu
    (adjoint_mem_peirce01 hp hu)).symm.trans (gram_kernel hp hu)

/-- Positive definiteness holds precisely when the two corner kernels intersect trivially. -/
theorem gram_posDef_iff (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    (u * uᴴ + uᴴ * u).PosDef ↔
      LinearMap.ker u.mulVecLin ⊓ LinearMap.ker uᴴ.mulVecLin = ⊥ := by
  constructor
  · intro hpos
    rw [← gram_kernel hp hu]
    exact LinearMap.ker_eq_bot.mpr
      (Matrix.mulVec_injective_iff_isUnit.mpr hpos.isUnit)
  · intro hker
    have hz : LinearMap.ker (u * uᴴ + uᴴ * u).mulVecLin = ⊥ :=
      (gram_kernel hp hu).trans hker
    have hps := gram_posSemidef u
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hps.isHermitian ?_
    intro x hx
    have hvalue : (u * uᴴ + uᴴ * u) *ᵥ x ≠ 0 := by
      intro hzero
      exact hx ((LinearMap.ker_eq_bot'.mp hz) x hzero)
    apply lt_of_le_of_ne (hps.dotProduct_mulVec_nonneg x)
    intro hzero
    exact hvalue (hps.dotProduct_mulVec_zero_iff.mp hzero.symm)

end InfoGeometry.Canonical.PeirceCouplingPositivity
