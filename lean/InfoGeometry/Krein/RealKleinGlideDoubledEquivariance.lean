/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBrillouinBase
import InfoGeometry.Krein.DoubledSpace

noncomputable section

namespace InfoGeometry.Krein.RealKleinGlideDoubledEquivariance

open KleinBrillouinBase
open InfoGeometry.Krein

/-!
# Real Klein glide to doubled-space equivariance

This is a cover-level finite readout.  It uses the existing affine Klein glide
and the canonical real doubled carrier; it does not identify the torus orbit
quotient with the Krein space or assert a descended quotient map.
-/

/-- A real coordinate readout into the canonical doubled Krein carrier. -/
def glideReadout (k : KleinBrillouinBase.Cover) : DoubledSpace ℝ :=
  to_doubled k.2 (-k.2)

/-- The affine Klein glide is intertwined with the canonical sheet swap. -/
theorem glideReadout_equivariant (k : KleinBrillouinBase.Cover) :
    glideReadout (glide k) = modular_j (glideReadout k) := by
  apply DoubledSpace.ext <;> simp [glideReadout, glide, modular_j]

end InfoGeometry.Krein.RealKleinGlideDoubledEquivariance

#print axioms InfoGeometry.Krein.RealKleinGlideDoubledEquivariance.glideReadout_equivariant
