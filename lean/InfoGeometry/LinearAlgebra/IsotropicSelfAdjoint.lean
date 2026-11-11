/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Self-adjoint maps with totally isotropic image

For a left-separating sesquilinear map, a self-adjoint endomorphism has
totally isotropic image exactly when its square is zero. If it is also
idempotent, it must vanish. No positivity, dimension, or commutativity of
the endomorphism algebra is assumed.
-/

namespace InfoGeometry.LinearAlgebra.IsotropicSelfAdjoint

variable {R V W : Type*} [CommSemiring R]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  {σ : R →+* R}

/-- For a self-adjoint endomorphism, total isotropy of the image is precisely
the square-zero condition. Left separation suffices. -/
theorem square_zero_iff_image_isotropic
    (B : V →ₗ[R] V →ₛₗ[σ] W) (hB : B.SeparatingLeft)
    (P : Module.End R V) (hself : B.IsSelfAdjoint P) :
    P * P = 0 ↔ ∀ x y : V, B (P x) (P y) = 0 := by
  constructor
  · intro hzero x y
    have hsq : P (P x) = 0 := DFunLike.congr_fun hzero x
    calc
      B (P x) (P y) = B (P (P x)) y := (hself (P x) y).symm
      _ = 0 := by simp only [hsq, map_zero, LinearMap.zero_apply]
  · intro hiso
    apply LinearMap.ext
    intro x
    change P (P x) = 0
    apply hB
    intro y
    rw [hself (P x) y]
    exact hiso x y

/-- An idempotent with totally isotropic image cannot be a nonzero
self-adjoint endomorphism of a left-separating sesquilinear space. -/
theorem eq_zero_of_idempotent_of_image_isotropic
    (B : V →ₗ[R] V →ₛₗ[σ] W) (hB : B.SeparatingLeft)
    {P : Module.End R V} (hP : IsIdempotentElem P)
    (hself : B.IsSelfAdjoint P)
    (hiso : ∀ x y : V, B (P x) (P y) = 0) : P = 0 := by
  calc
    P = P * P := hP.eq.symm
    _ = 0 := (square_zero_iff_image_isotropic B hB P hself).2 hiso

end InfoGeometry.LinearAlgebra.IsotropicSelfAdjoint
