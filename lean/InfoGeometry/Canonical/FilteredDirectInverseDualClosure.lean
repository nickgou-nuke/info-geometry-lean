/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredDirectInverseColimit

noncomputable section

namespace FilteredColimit.InductiveCocone

variable {R : Type*} [CommRing R]
variable {I : Type*} [Preorder I]
variable {A : I → Type*}
variable [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]

/-- Precomposition along an identity transition is the identity on the dual stage. -/
theorem dual_inverse_id
    (sys : DirectInductiveSystem R I A) (i : I)
    (phi : A i →ₗ[R] R) :
    dualInverseTransition sys (le_refl i) phi = phi := by
  ext x
  change phi (sys.f (le_refl i) x) = phi x
  rw [sys.f_id]
  rfl

/-- Dual transition maps preserve composition in the contravariant direction. -/
theorem dual_inverse_comp_map
    (sys : DirectInductiveSystem R I A)
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (dualInverseTransition sys hij).comp
        (dualInverseTransition sys hjk) =
      dualInverseTransition sys (le_trans hij hjk) := by
  ext phi x
  change phi (sys.f hjk (sys.f hij x)) = phi (sys.f (le_trans hij hjk) x)
  exact congrArg phi (congrArg (fun f : A i →ₗ[R] A k => f x) (sys.f_comp hij hjk))

end FilteredColimit.InductiveCocone
