/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- CliffordExteriorEquiv.lean
-- Equivalence between Clifford algebra `CliffordAlgebra Q` and exterior algebra `ExteriorAlgebra R M`.

import Mathlib.LinearAlgebra.CliffordAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra

open CliffordAlgebra
open ExteriorAlgebra

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- The genuine equivalence of Clifford algebra `CliffordAlgebra Q` with the exterior algebra.
    This is provided by Mathlib as `CliffordAlgebra.equivExterior`. -/

def cliffordExteriorEquiv : CliffordAlgebra Q ≃ₐ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.equivExterior Q

@[simp] lemma cliffordExteriorEquiv_apply (x : CliffordAlgebra Q) :
    cliffordExteriorEquiv Q x = CliffordAlgebra.equivExterior Q x := rfl

@[simp] lemma cliffordExteriorEquiv_symm_apply (x : ExteriorAlgebra R M) :
    (cliffordExteriorEquiv Q).symm x = (CliffordAlgebra.equivExterior Q).symm x := rfl

end InfoGeometry.Canonical
