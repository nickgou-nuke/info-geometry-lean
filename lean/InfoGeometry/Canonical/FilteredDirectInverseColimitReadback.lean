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
variable {A : I → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable {sys : DirectInductiveSystem R I A}
variable {A_inf : Type*} [AddCommGroup A_inf] [Module R A_inf]
variable (cocone : InductiveCocone R sys A_inf)

/-- A functional on the cocone target restricts to a compatible inverse family
of stage functionals. -/
theorem dualInverseTransition_comp_cocone
    (phi_inf : A_inf →ₗ[R] R) {i j : I} (hij : i ≤ j) :
    dualInverseTransition sys hij (phi_inf.comp (cocone.psi j)) =
      phi_inf.comp (cocone.psi i) := by
  ext x
  change phi_inf (cocone.psi j (sys.f hij x)) = phi_inf (cocone.psi i x)
  rw [cocone.cocone_eval_comm hij x]

end FilteredColimit.InductiveCocone
