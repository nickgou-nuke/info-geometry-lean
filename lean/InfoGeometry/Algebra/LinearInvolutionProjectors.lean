/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

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
  have hscalar : half * 2 = 1 := by simpa [mul_comm] using hhalf
  calc
    half • (x + u x) + half • (x - u x) =
        half • ((x + u x) + (x - u x)) := by
          simp only [smul_add, smul_sub]
    _ = half • ((2 : R) • x) := by congr 1; module
    _ = x := by rw [smul_smul, hscalar, one_smul]

/-- Every vector decomposes into its two involution projector components. -/
theorem decomposition {u : M →ₗ[R] M} {half : R}
    (hhalf : 2 * half = 1) (x : M) :
    x = plus u half x + minus u half x := by
  have h := LinearMap.congr_fun (plus_add_minus (u := u) hhalf) x
  exact h.symm

/-- Their difference reconstructs the involution. -/
theorem plus_sub_minus {u : M →ₗ[R] M} {half : R}
    (hhalf : 2 * half = 1) :
    plus u half - minus u half = u := by
  ext x
  change half • (x + u x) - half • (x - u x) = u x
  have hscalar : half * 2 = 1 := by simpa [mul_comm] using hhalf
  calc
    half • (x + u x) - half • (x - u x) =
        half • ((x + u x) - (x - u x)) := by
          simp only [smul_add, smul_sub]
    _ = half • ((2 : R) • u x) := by congr 1; module
    _ = u x := by rw [smul_smul, hscalar, one_smul]

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

/-- The positive linear projector is idempotent. -/
theorem plus_comp_plus {u : M →ₗ[R] M} {half : R}
    (hhalf : 2 * half = 1) (hu : u.comp u = LinearMap.id) :
    (plus u half).comp (plus u half) = plus u half := by
  ext x
  have he : u ((plus u half) x) = (plus u half) x := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (involution_mul_plus (u := u) (half := half) hu) x
  change half • ((plus u half) x + u ((plus u half) x)) = (plus u half) x
  rw [he]
  have hscalar : half * 2 = 1 := by simpa [mul_comm] using hhalf
  rw [show (plus u half) x + (plus u half) x = (2 : R) • (plus u half) x by module]
  rw [smul_smul, hscalar, one_smul]

/-- The negative linear projector is idempotent. -/
theorem minus_comp_minus {u : M →ₗ[R] M} {half : R}
    (hhalf : 2 * half = 1) (hu : u.comp u = LinearMap.id) :
    (minus u half).comp (minus u half) = minus u half := by
  ext x
  have he : u ((minus u half) x) = -(minus u half) x := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (involution_mul_minus (u := u) (half := half) hu) x
  change half • ((minus u half) x - u ((minus u half) x)) = (minus u half) x
  rw [he]
  have hscalar : half * 2 = 1 := by simpa [mul_comm] using hhalf
  rw [show (minus u half) x - -(minus u half) x = (2 : R) • (minus u half) x by module]
  rw [smul_smul, hscalar, one_smul]

/-- The two linear projectors are orthogonal in the `plus`-then-`minus` order. -/
theorem plus_comp_minus {u : M →ₗ[R] M} {half : R}
    (hu : u.comp u = LinearMap.id) :
    (plus u half).comp (minus u half) = 0 := by
  ext x
  have he : u ((minus u half) x) = -(minus u half) x := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (involution_mul_minus (u := u) (half := half) hu) x
  change half • ((minus u half) x + u ((minus u half) x)) = 0
  rw [he]
  simp

/-- The two linear projectors are orthogonal in the reverse order. -/
theorem minus_comp_plus {u : M →ₗ[R] M} {half : R}
    (hu : u.comp u = LinearMap.id) :
    (minus u half).comp (plus u half) = 0 := by
  ext x
  have he : u ((plus u half) x) = (plus u half) x := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (involution_mul_plus (u := u) (half := half) hu) x
  change half • ((plus u half) x - u ((plus u half) x)) = 0
  rw [he]
  simp

end InfoGeometry.Algebra.LinearInvolutionProjectors
