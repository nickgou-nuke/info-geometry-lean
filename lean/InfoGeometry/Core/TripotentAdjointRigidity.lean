/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentAdjoint

/-!
# Double-adjoint rigidity for a tripotent

The existing quintic annihilator has a simple zero root. Consequently the
kernel of the square of the adjoint is already the kernel of the adjoint.
The statement concerns the full associative real algebra and requires no
positive inner product, finite dimension, or commuting-operator assumption.
-/

namespace InfoGeometry.Core.TripotentAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The adjoint of a tripotent has no nonzero generalized zero-eigenvectors
of order two. The proof uses the existing quintic on the full algebra. -/
theorem ad_sq_apply_eq_zero_iff {S : A} (hS : S * S * S = S) (X : A) :
    (LieAlgebra.ad ℝ A S ^ 2) X = 0 ↔ LieAlgebra.ad ℝ A S X = 0 := by
  let D : Module.End ℝ A := LieAlgebra.ad ℝ A S
  constructor
  · intro h
    have h2 : D (D X) = 0 := h
    have h3 : (D ^ 3) X = 0 := by
      change D (D (D X)) = 0
      rw [h2, map_zero]
    have h5 : (D ^ 5) X = 0 := by
      change D (D (D (D (D X)))) = 0
      rw [h2, map_zero, map_zero, map_zero]
    have hq := LinearMap.congr_fun (ad_quintic hS) X
    change (D ^ 5) X - (5 : ℝ) • ((D ^ 3) X) + (4 : ℝ) • (D X) = 0 at hq
    rw [h5, h3, smul_zero, sub_zero, zero_add] at hq
    rcases smul_eq_zero.mp hq with hfour | hzero
    · norm_num at hfour
    · exact hzero
  · intro h
    change D (D X) = 0
    have h1 : D X = 0 := h
    rw [h1, map_zero]

/-- Squaring the native adjoint of a tripotent leaves its kernel unchanged. -/
theorem ker_ad_sq_eq_ker_ad {S : A} (hS : S * S * S = S) :
    LinearMap.ker (LieAlgebra.ad ℝ A S ^ 2) =
      LinearMap.ker (LieAlgebra.ad ℝ A S) := by
  ext X
  simp only [LinearMap.mem_ker, ad_sq_apply_eq_zero_iff hS]

end InfoGeometry.Core.TripotentAdjoint
