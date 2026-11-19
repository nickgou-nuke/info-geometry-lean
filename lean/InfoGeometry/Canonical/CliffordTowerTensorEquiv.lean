/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- CliffordTowerTensorEquiv.lean
-- Equivalence between the Clifford tower and a tensor product.

import Mathlib.LinearAlgebra.CliffordAlgebra
import Mathlib.Algebra.Algebra.TensorProduct

open CliffordAlgebra TensorProduct

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)

/-- The tower equivalence: `CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] CliffordAlgebra Q₁ ⊗[R] CliffordAlgebra Q₂`.
    This is provided by Mathlib as `CliffordAlgebra.towerEquivTensor`. -/

def cliffordTowerTensorEquiv :
    CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] CliffordAlgebra Q₁ ⊗[R] CliffordAlgebra Q₂ :=
  CliffordAlgebra.towerEquivTensor Q₁ Q₂

@[simp] lemma cliffordTowerTensorEquiv_apply (x) :
    cliffordTowerTensorEquiv Q₁ Q₂ x = CliffordAlgebra.towerEquivTensor Q₁ Q₂ x := rfl

end InfoGeometry.Canonical
