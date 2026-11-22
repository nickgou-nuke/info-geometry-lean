/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.G2ToBraidChain
import InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame

/-!
# Chiral stabilizer for `G₂(₂)` derivations

The derivation carrier and the chiral complex structure are owned by existing
modules.  This file records the stabilizer predicate at the chiral involution,
replacing the vacuous placeholders of the pre-integration snapshot.
-/

noncomputable section

namespace InfoGeometry.Canonical.G2DerivationFlowBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame

/-- A derivation stabilizes the chiral complex structure when it annihilates it. -/
def g2StabilizerOfI (D : G2ToBraidChain.G2Derivation) : Prop :=
  D.toLinearMap (chiralI (R := ℝ)) = 0

end InfoGeometry.Canonical.G2DerivationFlowBridge
