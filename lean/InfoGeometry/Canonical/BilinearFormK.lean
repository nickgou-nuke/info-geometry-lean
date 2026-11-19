/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- BilinearFormK.lean
-- Family of bilinear forms ⟪·,·⟫ₖ indexed by a natural number `k`.

import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.Algebra.Algebra.Basic

open scoped Matrix

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The bilinear form `⟪x, y⟫ₖ = k • (0 : R)` – i.e. the zero form scaled by `k`. 
    This placeholder satisfies all bilinear axioms and can later be replaced by a concrete form. -/

def bilinearFormK (k : ℕ) : BilinForm R M :=
  (0 : BilinForm R M).smul (k : R)

@[simp] lemma bilinearFormK_apply (k : ℕ) (x y : M) :
    bilinearFormK k x y = (k : R) • (0 : R) := rfl

end InfoGeometry.Canonical
