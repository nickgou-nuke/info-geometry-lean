/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Omega.GU.TerminalGamma6Rigidity
import Omega.GU.Window6IntrinsicBracketFiniteIntegerReduction

namespace Omega.GU

/-- Package combining the intrinsic-bracket finite-integer reduction with terminal `Γ₆` rigidity.
    prop:window6-bracket-certificate-reduction -/
theorem paper_window6_bracket_certificate_reduction
    (D : Omega.GU.Window6IntrinsicBracketFiniteIntegerReductionData)
    (R : Omega.GU.TerminalGamma6RigidityData) :
    (∀ c, c ∈ D.finiteIntegerSystem → ∀ i k, c i i k = 0) ∧
      R.automorphismGroupTrivial := by
  refine ⟨?_, ?_⟩
  · intro c hc i k
    exact window6_antisymmetry_forces_diagonal_structure_constants_zero D c hc i k
  exact (paper_terminal_gamma6_rigidity R).2

end Omega.GU
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
