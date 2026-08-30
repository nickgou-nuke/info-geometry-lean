/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Complex.MobiusApolloniusFoliation

/-!
# Cayley–Apollonius Möbius Conjugacy

The fixed transition map `C z = -(z + 3) / (3z + 1)` identifies the
Riemann–Cayley coordinate `s / (1 - s)` with the midpoint Apollonius map.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyApolloniusConjugacy

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Complex.MobiusApollonius

def cayleyApolloniusTransition (z : ℂ) : ℂ :=
  -(z + 3) / (3 * z + 1)

theorem mobiusMap_eq_cayleyApolloniusTransition
    (s : ℂ) (hs : 1 - s ≠ 0) :
    mobiusMap s = cayleyApolloniusTransition (cayleyToFugacity s) := by
  unfold mobiusMap cayleyApolloniusTransition cayleyToFugacity at *
  field_simp [hs]
  ring

end InfoGeometry.Canonical.CayleyApolloniusConjugacy
