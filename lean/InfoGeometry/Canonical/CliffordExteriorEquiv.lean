/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- CliffordExteriorEquiv.lean
-- Equivalence between Clifford algebra `CliffordAlgebra Q` and exterior algebra `ExteriorAlgebra R M`.

import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

open CliffordAlgebra
open ExteriorAlgebra

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- The characteristic-not-two linear equivalence between the Clifford carrier
and the exterior carrier. It does not identify their products: Clifford
multiplication and exterior wedge multiplication remain distinct. -/

def cliffordExteriorEquiv : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.equivExterior Q

@[simp] lemma cliffordExteriorEquiv_apply (x : CliffordAlgebra Q) :
    cliffordExteriorEquiv Q x = CliffordAlgebra.equivExterior Q x := rfl

@[simp] lemma cliffordExteriorEquiv_symm_apply (x : ExteriorAlgebra R M) :
    (cliffordExteriorEquiv Q).symm x = (CliffordAlgebra.equivExterior Q).symm x := rfl

end InfoGeometry.Canonical
