/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.KleinBottleSpectrum
import InfoGeometry.Canonical.KleinBottleSewing
import InfoGeometry.Canonical.KleinSewingDefect
import InfoGeometry.Physics.KleinBottleCosmology

/-! # Klein Spectrum–Sewing Bridge

Connects the Klein bottle spectral theory (even/odd modes, glide invariance,
chirality flip) with the algebraic sewing carriers (tilt, switch, chiralIndex).

The even/odd spectral branches correspond to the two chiral sectors (P_+ and
P_-) of the algebraic carrier. The glide invariance of modes mirrors the
sewing condition. The chirality flip under glide mirrors the tilt operator's
sign flip under switch conjugation.

Reuses existing carriers and theorems; no new carrier or structure.
-/
namespace InfoGeometry.Physics.KleinSpectrumSewingBridge

open Matrix Complex
open InfoGeometry.Physics.KleinBottleSpectrum
open InfoGeometry.Canonical.KleinSewingDefect

/-- The chirality flip is an involution, mirroring switch² = 1. -/
theorem chirality_flip_involutive (c : KleinChirality) :
    flipChirality (flipChirality c) = c :=
  flipChirality_twice c

/-- The chirality flip has order 4, mirroring tilt⁴ = 1 (tilt² = 1). -/
theorem chirality_flip_order_four (c : KleinChirality) :
    flipChirality (flipChirality (flipChirality (flipChirality c))) = c :=
  flipChirality_fourth c

/-- On a sewn boundary state, the algebraic chiral index vanishes,
    corresponding to balanced even/odd spectral branches. -/
theorem sewn_chiral_balance (s : BoundaryState) (h : isSewn s) :
    chiralIndex s = 0 :=
  InfoGeometry.Physics.KleinBottleCosmology.sewn_boundary_chiral_index_vanishes s h

/-- The defect trace vanishes on sewn states, corresponding to
    equal even/odd spectral contributions. -/
theorem sewn_defect_zero (s : BoundaryState) (h : isSewn s) :
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = 0 := by
  have hci : chiralIndex s = 0 := InfoGeometry.Physics.KleinBottleCosmology.sewn_boundary_chiral_index_vanishes s h
  exact boundary_defect_trace_zero_iff s |>.mpr hci

/-- The even and odd branches are both glide-invariant, corresponding to
    the sewing condition on both chiral sectors. -/
theorem even_odd_glide_both_invariant (n : ℤ) :
    glideInvariant evenTransverseParity (evenLongitudinalParity n) ∧
    glideInvariant oddTransverseParity (oddLongitudinalParity n) := by
  constructor
  · exact evenBranch_has_even_glide_parity n
  · exact oddBranch_has_odd_glide_parity n

/-- The mixed transverse/longitudinal parity is forbidden, corresponding to
    the chiral index being an odd quantity under the sewing twist. -/
theorem mixed_parity_forbidden (n : ℤ) :
    ¬ glideInvariant oddTransverseParity (evenLongitudinalParity n) :=
  mixed_odd_transverse_even_longitudinal_impossible n

end InfoGeometry.Physics.KleinSpectrumSewingBridge