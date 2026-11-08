/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.DirectSum.Internal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Basic

/-!
# 5-Graded Decomposition of Affine Symmetry Algebras

This file defines the abstract structure for a 5-graded Lie algebra.
In physical applications (e.g. CFT), the full symmetry algebra (Virasoro ⋉ Affine Kac-Moody)
admits a natural 5-grading by conformal weight (L₀ eigenvalue) modulated by the
raising/lowering character of the operators.

The grading takes values in `Fin 5`, which we canonically identify with `{-2, -1, 0, 1, 2}`.

## Main definitions

* `VirasoroProject.FiveGradedAlgebra`: The structure encapsulating a Lie algebra with a 5-grading.
-/

namespace VirasoroProject

/-- The abstract structure of a 5-graded Lie algebra, corresponding to the
decomposition of the Sugawara-extended affine Kac-Moody algebra into:
- Grade 0 (-2): Virasoro lowering
- Grade 1 (-1): Current algebra lowering
- Grade 2 ( 0): Cartan + central
- Grade 3 (+1): Current algebra raising
- Grade 4 (+2): Virasoro raising
-/
structure FiveGradedAlgebra (𝕜 : Type*) [Field 𝕜] where
  /-- The full algebra -/
  algebra : Type*
  [instLieRing : LieRing algebra]
  [instLieAlgebra : LieAlgebra 𝕜 algebra]
  
  /-- The five graded pieces. -/
  grade : Fin 5 → Submodule 𝕜 algebra
  
  /-- The grading is a direct sum decomposition of the underlying module. -/
  directSum : DirectSum.IsInternal grade
  
  /-- Compatibility of the Lie bracket with the grading.
  Instead of full Z-grading, since it truncates at ±2, we just say:
  if `i + j - 4` is between 0 and 4, it lands in that grade; otherwise it's 0.
  We express this compactly by saying that the bracket of grade `i` and `j`
  is contained in `grade k` if `k = i + j - 2` (where grades are 0..4).
  For simplicity, we provide a predicate for when the bracket must be zero. -/
  bracket_zero : ∀ i j, (i.val + j.val < 2 ∨ i.val + j.val > 6) →
    ∀ x ∈ grade i, ∀ y ∈ grade j, ⁅x, y⁆ = 0
  
  /-- When the grades add up to a valid grade, the bracket lands there. -/
  bracket_compat : ∀ i j k, i.val + j.val = k.val + 2 →
    ∀ x ∈ grade i, ∀ y ∈ grade j, ⁅x, y⁆ ∈ grade k

end VirasoroProject
