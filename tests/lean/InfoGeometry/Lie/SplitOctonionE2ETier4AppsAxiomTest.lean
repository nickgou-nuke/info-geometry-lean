/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.GradedDualNullconeOperatorAlgebra
import InfoGeometry.Canonical.SplitOctonionCayleyDickson
import InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR
import InfoGeometry.Lie.SplitOctonionCl33G2Stabilizer
import InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InfoGeometry.Lie.SplitOctonionE2ETier4AppsAxiomTest

open InfoGeometry.Canonical.SplitOctonionCayleyDickson
open InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge

 theorem graded_operator_owner_imports :
    Nonempty (InfoGeometry.Canonical.GradedDualNullconeOperatorAlgebra.NullconeCarrier 1) := by
  exact ⟨0⟩

theorem left_action_boundary
    (x y : InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR.Oct) :
    zornLeftActMatrix x * zornLeftActMatrix y +
        zornLeftActMatrix y * zornLeftActMatrix x =
      zornLeftActMatrix (zornAdd (zornMul x y) (zornMul y x)) :=
  zornLeftActMatrix_anticommutator x y

theorem stabilizer_owner_imports :
    Nonempty SplitOctCD := by
  exact ⟨0⟩

theorem daviau_left_and_right_embeddings :
    Function.Injective ⇑cl33ToCl44EvenLeft ∧
      Function.Injective ⇑cl33ToCl44EvenRight :=
  ⟨cl33_embeds_into_cl44EvenLeft, cl33_embeds_into_cl44EvenRight⟩

theorem tensor_and_peirce_contracts :
    Nonempty (Function.Injective ⇑cl33ToCl44EvenLeft) := by
  exact ⟨cl33_embeds_into_cl44EvenLeft⟩

end InfoGeometry.Lie.SplitOctonionE2ETier4AppsAxiomTest
