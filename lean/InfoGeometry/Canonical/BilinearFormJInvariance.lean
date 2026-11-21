/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- BilinearFormJInvariance.lean
-- J‑invariance of the `bilinearFormK` family.

import Mathlib.LinearAlgebra.BilinearForm.Basic
import InfoGeometry.Canonical.BilinearFormK

open InfoGeometry.Canonical

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A linear involution `J` on `M` (i.e. `J ∘ J = id`). -/
class InvolutiveLinearMap (J : M →ₗ[R] M) : Prop where
  involutive : Function.Involutive J

/-- `bilinearFormK` is invariant under any involutive linear map `J`. -/
theorem bilinearFormK_J_invariant (J : M →ₗ[R] M) [InvolutiveLinearMap J] (k : ℕ) (x y : M) :
    bilinearFormK (R:=R) (M:=M) k (J x) (J y) = bilinearFormK (R:=R) (M:=M) k x y := by
  unfold bilinearFormK
  simp

end InfoGeometry.Canonical
