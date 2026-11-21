/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- CliffordTowerTensorEquiv.lean
-- Equivalence between the Clifford tower and a tensor product.

import Mathlib.LinearAlgebra.CliffordAlgebra.Prod

open CliffordAlgebra
open scoped TensorProduct

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)

/-- The Clifford algebra of an orthogonal direct sum is the **Koszul-graded** tensor
product of the two Clifford algebras. The grading is essential: odd generators from
the two orthogonal summands anticommute. -/

noncomputable def cliffordTowerTensorEquiv :
    CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R]
      (CliffordAlgebra.evenOdd Q₁ ᵍ⊗[R] CliffordAlgebra.evenOdd Q₂) :=
  CliffordAlgebra.prodEquiv Q₁ Q₂

omit [Invertible (2 : R)] in
@[simp] lemma cliffordTowerTensorEquiv_apply (x) :
    cliffordTowerTensorEquiv Q₁ Q₂ x = CliffordAlgebra.prodEquiv Q₁ Q₂ x := rfl

end InfoGeometry.Canonical
