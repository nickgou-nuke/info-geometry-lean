/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.GradedGraceContraction

/-!
# Basis-free Shirokov scalar-part core

This owner defines Shirokov's rank-zero extraction directly on
`CliffordAlgebra Q`, without choosing a matrix representation.  The scalar
part is transported from the exterior-algebra augmentation through the
existing `CliffordAlgebra.equivExterior` linear equivalence.

The recurrence of Faddeev--LeVerrier/Shirokov type will be built on this core.
No proof bypasses or extra assumptions are introduced here.
-/

noncomputable section

namespace InfoGeometry.Clifford.ShirokovBasisFreeCore

open InfoGeometry.Clifford.GradedGraceContraction

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)]
variable (Q : QuadraticForm R M)

/-- Basis-free scalar part of a Clifford multivector. -/
def scalarPart : CliffordAlgebra Q →ₗ[R] R :=
  (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R).toLinearMap.comp
    (CliffordAlgebra.equivExterior (Q := Q)).toLinearMap

/-- Shirokov's normalized Clifford trace for a chosen representation degree `N`. -/
def shirokovTrace (N : ℕ) : CliffordAlgebra Q →ₗ[R] R :=
  (N : R) • scalarPart Q

theorem shirokovTrace_apply (N : ℕ) (x : CliffordAlgebra Q) :
    shirokovTrace Q N x = (N : R) * scalarPart Q x := by
  simp [shirokovTrace]

/-- The scalar part extracts the algebra-map scalar exactly. -/
@[simp] theorem scalarPart_algebraMap (r : R) :
    scalarPart Q (algebraMap R (CliffordAlgebra Q) r) = r := by
  simp [scalarPart]

/-- The scalar part annihilates Clifford vectors. -/
@[simp] theorem scalarPart_ι (m : M) :
    scalarPart Q (CliffordAlgebra.ι Q m) = 0 := by
  simp [scalarPart, ExteriorAlgebra.algebraMapInv]

/-- The Shirokov trace extracts the representation-degree-scaled scalar exactly. -/
@[simp] theorem shirokovTrace_algebraMap (N : ℕ) (r : R) :
    shirokovTrace Q N (algebraMap R (CliffordAlgebra Q) r) = (N : R) * r := by
  simp [shirokovTrace, scalarPart_algebraMap]

/-- The scalar part is the rank-zero exterior grade projection read back into `R`. -/
theorem exteriorGradeProj_zero_eq_scalarPart (x : CliffordAlgebra Q) :
    exteriorGradeProj R M 0 (CliffordAlgebra.equivExterior (Q := Q) x) =
      algebraMap R (ExteriorAlgebra R M) (scalarPart Q x) := by
  exact exteriorGradeProj_zero_eq_algebraMap_algebraMapInv
    (CliffordAlgebra.equivExterior (Q := Q) x)

/-- The scalar part of a product of two Clifford vectors is the associated
bilinear coefficient of `-Q`, with the sign forced by the change of form. -/
theorem scalarPart_ι_mul_ι (m n : M) :
    scalarPart Q (CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q n) =
      -((QuadraticMap.associated (R := R) (M := M) (-Q)) m n) := by
  simp [scalarPart, CliffordAlgebra.equivExterior,
    CliffordAlgebra.changeFormEquiv, CliffordAlgebra.changeForm_ι_mul_ι,
    ExteriorAlgebra.algebraMapInv]

/-- The scalar vector product is symmetric, as required by the cyclic trace law. -/
theorem scalarPart_ι_mul_ι_comm (m n : M) :
    scalarPart Q (CliffordAlgebra.ι Q m * CliffordAlgebra.ι Q n) =
      scalarPart Q (CliffordAlgebra.ι Q n * CliffordAlgebra.ι Q m) := by
  rw [scalarPart_ι_mul_ι, scalarPart_ι_mul_ι]
  congr 1
  exact (QuadraticForm.associated_isSymm (S := R) (-Q)).eq m n

end InfoGeometry.Clifford.ShirokovBasisFreeCore
