/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Thermodynamics.SouriauApolloniusEntropyFoliation
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Souriau Foliation & Apollonius Entropy Leaves Capstone (Canonical Export)

Canonical umbrella export connecting Souriau symplectic thermodynamic leaves,
Möbius-Apollonius foliation on the critical line, Poincaré Fisher-Rao geometry,
and topological Yang-Baxter integrability.
-/

namespace InfoGeometry.Canonical.SouriauApolloniusEntropyFoliation

open InfoGeometry.Thermodynamics.SouriauApolloniusFoliation

/-- Forwarding of the grand synthesis theorem. -/
abbrev grand_canonical_souriau_apollonius_foliation_synthesis :=
  @grand_souriau_apollonius_foliation_synthesis

end InfoGeometry.Canonical.SouriauApolloniusEntropyFoliation
