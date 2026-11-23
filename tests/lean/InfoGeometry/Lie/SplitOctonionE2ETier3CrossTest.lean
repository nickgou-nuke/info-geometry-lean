/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitOctonionCayleyDickson
import InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
import InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge
import InfoGeometry.Clifford.RealSpacetimeQuaternion

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InfoGeometry.Lie.SplitOctonionE2ETier3CrossTest

open InfoGeometry.Canonical.SplitOctonionCayleyDickson
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge

 theorem zorn_transport_preserves_mul (x y : SplitOctCD) :
    splitOctCDEquivZornSplitOctonion (x * y) =
      zornMul (splitOctCDEquivZornSplitOctonion x)
        (splitOctCDEquivZornSplitOctonion y) :=
  splitOctCDEquivZornSplitOctonion_mul x y

theorem fock_transport_is_equivalence :
    Nonempty (Exterior3 ≃ₗ[ℝ]
      InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.CZ) := by
  exact ⟨fockBdGEquiv⟩

theorem clifford_left_embedding :
    Function.Injective ⇑cl33ToCl44EvenLeft :=
  cl33_embeds_into_cl44EvenLeft

theorem quaternion_realization_is_noncommutative :
    HestenesCl14.gamma 1 * HestenesCl14.gamma 2 ≠
      HestenesCl14.gamma 2 * HestenesCl14.gamma 1 :=
  InfoGeometry.Clifford.RealSpacetimeQuaternion.gamma_one_two_ne

end InfoGeometry.Lie.SplitOctonionE2ETier3CrossTest
