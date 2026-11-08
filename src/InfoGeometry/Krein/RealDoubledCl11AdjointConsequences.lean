/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.RealDoubledOperatorAdjointTransport
import InfoGeometry.Krein.Clifford

/-!
# Krein-adjoint consequences for the transported real `Cl(1,1)` action

This file keeps the proved operator-level content separate from unresolved
basis-identification claims.  The canonical doubled generators are transported
through the existing real Hilbert/Krein equivalence, and their Krein
self-adjointness is proved by the existing adjoint transport theorem.
-/

namespace InfoGeometry.Krein.RealDoubledCl11AdjointConsequences

open InfoGeometry.Krein
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem conjugateDoubledEnd_K :
    conjugateDoubledEnd (E := E)
        (Quantum.doubledSpaceCl11Action (E := E)).K =
      (hilbertDoubledCl11Action (E := E)).K := by
  change conjugateDoubledEnd (E := E)
      ((Quantum.doubledSpaceCl11Action (E := E)).J.comp
        (Quantum.doubledSpaceCl11Action (E := E)).eps) = _
  rw [conjugateDoubledEnd_comp, conjugateDoubledEnd_J,
    conjugateDoubledEnd_eps]
  rfl

theorem hilbertDoubledCl11Action_eps_isKreinSelfAdjoint :
    KreinSpace.IsKreinSelfAdjoint
      (hilbertDoubledCl11Action (E := E)).eps := by
  rw [← conjugateDoubledEnd_eps (E := E)]
  rw [Quantum.doubledSpaceCl11Action_eps]
  rw [conjugateDoubledEnd_spectral_epsilon_jCLM (E := E)]
  exact kreinAdjoint_jCLM_hilbert (E := E)

theorem hilbertDoubledCl11Action_K_isKreinSelfAdjoint :
    KreinSpace.IsKreinSelfAdjoint
      (hilbertDoubledCl11Action (E := E)).K := by
  change KreinSpace.kreinAdjoint (hilbertComplexI (E := E)) =
    hilbertComplexI (E := E)
  exact kreinAdjoint_hilbertComplexI (E := E)

end InfoGeometry.Krein.RealDoubledCl11AdjointConsequences
