/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- TauQDefinition.lean
-- Definition of the scalar functional `τ_Q` via the bilinear form family.

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Canonical.BilinearFormK

open InfoGeometry.Canonical

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- `τ_Q` is defined as the diagonal of the `k = 0` bilinear form.
    For now this yields the zero map, but the definition is ready for a concrete implementation. -/

def tau_Q (x : M) : R :=
  bilinearFormK (R:=R) (M:=M) 0 x x

@[simp] lemma tau_Q_zero (x : M) : tau_Q (R:=R) (M:=M) x = (0 : R) := by
  unfold tau_Q
  simp [bilinearFormK_apply]

end InfoGeometry.Canonical
