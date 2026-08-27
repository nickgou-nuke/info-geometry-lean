/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# Linear involution projectors

The scalar involution formulas in `CyclotomicOperatorProjectors` lift directly
to endomorphisms of a module.  This is the concrete `C₂` operator layer; it
does not claim a Fourier decomposition for arbitrary finite order.
-/

namespace InfoGeometry.Algebra.LinearInvolutionProjectors

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The `+1` projector associated to an involution and a chosen half. -/
def plus (u : M →ₗ[R] M) (half : R) : M →ₗ[R] M :=
  half • (LinearMap.id + u)

/-- The `-1` projector associated to an involution and a chosen half. -/
def minus (u : M →ₗ[R] M) (half : R) : M →ₗ[R] M :=
  half • (LinearMap.id - u)

/-- The two linear projectors sum to the identity when `2 * half = 1`. -/
theorem plus_add_minus {u : M →ₗ[R] M} {half : R}
    (hhalf : 2 * half = 1) :
    plus u half + minus u half = LinearMap.id := by
  ext x
  change half • (x + u x) + half • (x - u x) = x
  rw [← add_smul]
  have hscalar : half * 2 = 1 := by simpa [mul_comm] using hhalf
  rw [show (x + u x) + (x - u x) = 2 • x by module]
  rw [smul_smul, hscalar, one_smul]

/-- Their difference reconstructs the involution. -/
theorem plus_sub_minus {u : M →ₗ[R] M} {half : R}
    (hhalf : 2 * half = 1) :
    plus u half - minus u half = u := by
  ext x
  change half • (x + u x) - half • (x - u x) = u x
  rw [← sub_smul]
  have hscalar : half * 2 = 1 := by simpa [mul_comm] using hhalf
  rw [show (x + u x) - (x - u x) = 2 • u x by module]
  rw [smul_smul, hscalar, one_smul]

/-- The involution acts by `+1` on the positive projector. -/
theorem involution_mul_plus {u : M →ₗ[R] M} {half : R}
    (hu : u.comp u = LinearMap.id) :
    u.comp (plus u half) = plus u half := by
  ext x
  have hux : u (u x) = x := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hu x
  simp [plus, LinearMap.comp_apply, hux]
  module

/-- The involution acts by `-1` on the negative projector. -/
theorem involution_mul_minus {u : M →ₗ[R] M} {half : R}
    (hu : u.comp u = LinearMap.id) :
    u.comp (minus u half) = -(minus u half) := by
  ext x
  have hux : u (u x) = x := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hu x
  simp [minus, LinearMap.comp_apply, hux]
  module

end InfoGeometry.Algebra.LinearInvolutionProjectors
