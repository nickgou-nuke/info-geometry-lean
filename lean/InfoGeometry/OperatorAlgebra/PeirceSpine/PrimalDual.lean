/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent

/-!
# Primal and dual chord potentials in the Peirce operator spine

The graph-transformed idempotents `Ad(1 + N₊)(P)` and `Ad(1 + N₋)(P)` determine
ordered chord products. This file identifies those products with the two
Peirce corner cycles `Q₊` and `Q₋`, then reads their sum and difference as `V`
and `Σ`. The statements concern an arbitrary associative ring and an
idempotent; no convexity or analytic partition function is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- The ordered chord products of the two graph transforms are exactly the
upper and lower Peirce cycles. Their sum and difference are the mass `V` and
the commutator component `Σ`. -/
theorem archetype_A42_primal_dual_chord_potentials (A C : B) :
    (P - conjPlus P A P) * (conjMinus P C P - P) = qgtPlus P A C ∧
    (conjMinus P C P - P) * (P - conjPlus P A P) = qgtMinus P A C ∧
    qgtPlus P A C + qgtMinus P A C = genV P A C ∧
    qgtPlus P A C - qgtMinus P A C = genSig P A C := by
  simp only [conjPlus, conjMinus, qgtPlus, qgtMinus]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
