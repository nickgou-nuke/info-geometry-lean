/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitOctonionCayleyDickson
import InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR
import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InfoGeometry.Lie.SplitOctonionE2ETier2BoundaryTest

open InfoGeometry.Canonical.SplitOctonionCayleyDickson
open InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge
open InfoGeometry.Lie.SplitOctonionEllPolarization

 theorem carrier_is_nonassociative :
    ∃ x y z : SplitOctCD, x * (y * z) ≠ (x * y) * z :=
  ⟨iCD 0, iCD 1, ellCD, Ne.symm splitOctCD_nonassociative⟩

theorem left_matrix_is_noncommutative :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A :=
  matrix8_noncommutative

theorem right_root_off_diagonal {i j : Fin 3} (h : i ≠ j) :
    rightRegular (rootMinus j) * rightRegular (rootPlus i) +
        rightRegular (rootPlus i) * rightRegular (rootMinus j) = 0 :=
  rightRegular_root_anticommutator_off_diagonal (i := i) (j := j) h

theorem daviau_embeddings_are_injective :
    Function.Injective ⇑cl33ToCl44EvenLeft ∧
      Function.Injective ⇑cl33ToCl44EvenRight :=
  ⟨cl33_embeds_into_cl44EvenLeft, cl33_embeds_into_cl44EvenRight⟩

end InfoGeometry.Lie.SplitOctonionE2ETier2BoundaryTest
