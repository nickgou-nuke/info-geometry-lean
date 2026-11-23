/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.GradedGraceContraction

/-!
# Basis-free Shirokov scalar-part core

This owner reuses the existing rank-zero trace `hTrace_cl` on
`CliffordAlgebra Q`, without choosing a matrix representation.  Its
exterior-algebra construction and grade-zero interpretation are owned by
`GradedGraceContraction`.

The recurrence of Faddeev--LeVerrier/Shirokov type will be built on this core.
The vector-pair trace identity is already owned by
`GradedGraceContraction.cliffordKreinPairing_ι_ι`; this file does not duplicate it.
-/

noncomputable section

namespace InfoGeometry.Clifford.ShirokovBasisFreeCore

open InfoGeometry.Clifford.GradedGraceContraction

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)]
variable (Q : QuadraticForm R M)

/-- Shirokov's normalized Clifford trace for a chosen representation degree `N`. -/
def shirokovTrace (N : ℕ) : CliffordAlgebra Q →ₗ[R] R :=
  (N : R) • InfoGeometry.Riemannian.hTrace_cl Q

theorem shirokovTrace_apply (N : ℕ) (x : CliffordAlgebra Q) :
    shirokovTrace Q N x =
      (N : R) * InfoGeometry.Riemannian.hTrace_cl Q x := by
  simp [shirokovTrace]

/-- The Shirokov trace extracts the representation-degree-scaled scalar exactly. -/
@[simp] theorem shirokovTrace_algebraMap (N : ℕ) (r : R) :
    shirokovTrace Q N (algebraMap R (CliffordAlgebra Q) r) = (N : R) * r := by
  simp [shirokovTrace, InfoGeometry.Riemannian.hTrace_cl]

end InfoGeometry.Clifford.ShirokovBasisFreeCore
