/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftMultiplicationDefect
import InfoGeometry.OperatorAlgebra.OperatorDefectCompletion

/-!
# Native Zorn defects belong to the generated operator Lie algebra

This adapter uses the repository's actual real Zorn carrier and its proved
commutator-defect identity. It does not assert that an arbitrary noncommutative-
coefficient Zorn product is alternative.

The underlying defect identities are owned by
`InfoGeometry.Algebra.ZornLeftMultiplicationDefect`; this file adds only the
closure-in-an-arbitrary-subalgebra and Peirce-odd consequences.
-/

set_option autoImplicit false

namespace InfoGeometry.Algebra.ZornLeftCAR

open ZornPinorReconstruction
open InfoGeometry.OperatorAlgebra.DefectCompletion

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

/-- Every operator Lie subalgebra containing all left actions contains their
associator defects. No defect is postulated as an independent generator. -/
theorem multiplicationDefect_mem_of_left_actions
    (K : LieSubalgebra ℝ (Module.End ℝ Z))
    (hL : ∀ W : Z, leftMultiplication W ∈ K) (X Y : Z) :
    multiplicationDefect X Y ∈ K := by
  rw [multiplicationDefect_eq_half_commutator_correction]
  exact K.smul_mem (1 / 2 : ℝ)
    (K.sub_mem (hL (ZornVectorMatrix.commutator X Y))
      (K.lie_mem (hL X) (hL Y)))

/-- If the operator idempotent is retained as well, the odd Peirce component
of the associator is generated inside the same operator Lie algebra. -/
theorem odd_multiplicationDefect_mem_of_left_actions
    (K : LieSubalgebra ℝ (Module.End ℝ Z))
    (hL : ∀ W : Z, leftMultiplication W ∈ K)
    (p : Module.End ℝ Z) (hp : p * p = p) (hpK : p ∈ K)
    (X Y : Z) :
    oddPart p (multiplicationDefect X Y) ∈ K := by
  exact oddPart_mem_of_mem K p (multiplicationDefect X Y) hp hpK
    (multiplicationDefect_mem_of_left_actions K hL X Y)

end
end InfoGeometry.Algebra.ZornLeftCAR
