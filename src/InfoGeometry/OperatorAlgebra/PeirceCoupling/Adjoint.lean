/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCoupling.Algebra
import InfoGeometry.OperatorAlgebra.PeirceCoupling.GramGeometry

/-!
# Actual adjoint coupling of orthogonal Peirce corners

Self-adjointness of the idempotent identifies the reversed corner of `aᴴ`
with the adjoint of the forward corner of `a`. The resulting square is a
genuine Gram sum. Nonzero corners cannot commute with their adjoints, while
positive definiteness requires the stronger trivial-common-kernel condition.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling

open Matrix InfoGeometry.Core.PeirceDecomposition
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p : Matrix n n ℂ} (hp : IsStarProjection p) (a : Matrix n n ℂ)

local notation "U" => component10 p a
local notation "V" => component01 p aᴴ

include hp

/-- This is the actual conjugate transpose, not a separately supplied reverse arrow. -/
theorem adjoint_reverse_corner : V = Uᴴ := by
  have hs : pᴴ = p := hp.isSelfAdjoint.star_eq
  simp only [component10, component01, complementIdempotent, conjTranspose_mul,
    conjTranspose_sub, conjTranspose_one, hs, mul_assoc]

theorem adjoint_coupling_sq : (U + V) ^ 2 = U * Uᴴ + Uᴴ * U := by
  rw [opposite_sum_sq hp.isIdempotentElem a aᴴ, adjoint_reverse_corner hp a]

theorem adjoint_coupling_posSemidef : ((U + V) ^ 2).PosSemidef := by
  rw [adjoint_coupling_sq hp a]
  exact gramSum_posSemidef U

theorem adjoint_coupling_ker :
    LinearMap.ker ((U + V) ^ 2).mulVecLin =
      LinearMap.ker (U).mulVecLin ⊓ LinearMap.ker Uᴴ.mulVecLin := by
  rw [adjoint_coupling_sq hp a, gramSum_ker]

/-- The self-adjoint odd operator and its square have the same harmonic kernel. -/
theorem adjoint_sum_ker :
    LinearMap.ker (U + V).mulVecLin =
      LinearMap.ker (U).mulVecLin ⊓ LinearMap.ker Uᴴ.mulVecLin := by
  have hs : (U + V)ᴴ = U + V := by
    rw [adjoint_reverse_corner hp a]
    simp only [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  rw [← adjoint_coupling_ker hp a]
  ext v
  simp only [LinearMap.mem_ker, mulVecLin_apply, pow_two]
  simpa only [hs] using (conjTranspose_mul_self_mulVec_eq_zero (U + V) v).symm

theorem adjoint_coupling_posDef_iff :
    ((U + V) ^ 2).PosDef ↔
      LinearMap.ker (U).mulVecLin ⊓ LinearMap.ker Uᴴ.mulVecLin = ⊥ := by
  rw [adjoint_coupling_sq hp a, gramSum_posDef_iff_ker_inf_eq_bot]

theorem adjoint_sum_isUnit_iff :
    IsUnit (U + V) ↔ ((U + V) ^ 2).PosDef := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  change Function.Injective (U + V).mulVecLin ↔ _
  rw [← LinearMap.ker_eq_bot, adjoint_sum_ker hp a, adjoint_coupling_posDef_iff hp a]

/-- The signed quadratic operator vanishes precisely when the actual corner does. -/
theorem adjoint_lie_eq_zero_iff : ⁅U, V⁆ = 0 ↔ U = 0 := by
  rw [← jordan_eq_zero_iff_lie_eq_zero hp.isIdempotentElem a aᴴ,
    adjoint_reverse_corner hp a, gramSum_eq_zero_iff]

/-- A nonzero square-zero orthogonal corner genuinely fails to commute with its adjoint. -/
theorem adjoint_corners_commute_iff : Commute U Uᴴ ↔ U = 0 := by
  change U * Uᴴ = Uᴴ * U ↔ U = 0
  rw [← sub_eq_zero]
  change ⁅U, Uᴴ⁆ = 0 ↔ U = 0
  rw [← adjoint_reverse_corner hp a]
  exact adjoint_lie_eq_zero_iff hp a

end InfoGeometry.OperatorAlgebra.PeirceCoupling
