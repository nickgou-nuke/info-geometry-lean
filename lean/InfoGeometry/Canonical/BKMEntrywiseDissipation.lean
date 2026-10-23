/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BKMEntrywiseOnsagerMobility
import InfoGeometry.Canonical.FreeEnergyDissipationRate

/-!
# Algebraic dissipation for entrywise BKM mobility

This instantiates the existing finite matrix system with the entrywise
logarithmic-mean multiplier. Its rate inequality is algebraic: no trajectory,
normalized density, or equivalence to operator Kubo--Mori transport is claimed.
-/
noncomputable section

namespace InfoGeometry.Canonical.EntrywiseBKMOnsagerMobility

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The native finite matrix system with the entrywise BKM mobility. -/
def bkmDissipativeSystem (energies : ι → ℝ)
    (rho H gradF : EntrywiseMat ι) :
    MetriplecticDissipation.MetriplecticDissipativeSystem ι where
  rho := rho
  H := H
  grad_F := gradF
  Onsager := bkmOnsager energies

/-- A vanishing reversible contribution leaves a nonpositive algebraic rate. -/
theorem bkm_freeEnergy_rate_nonpos
    (energies : ι → ℝ) (rho H gradF : EntrywiseMat ι)
    (hunitary :
      (trace (star gradF * (-Complex.I • (H * rho - rho * H)))).re = 0) :
    MetriplecticDissipation.freeEnergyRate
      (bkmDissipativeSystem energies rho H gradF) ≤ 0 := by
  apply MetriplecticDissipation.freeEnergy_rate_nonpos
  · intro X
    exact bkmOnsager_positive energies X
  · exact hunitary

/-- Zero Hamiltonian makes the reversible contribution vanish identically. -/
theorem bkm_pureDissipation_rate_nonpos
    (energies : ι → ℝ) (rho gradF : EntrywiseMat ι) :
    MetriplecticDissipation.freeEnergyRate
      (bkmDissipativeSystem energies rho 0 gradF) ≤ 0 := by
  apply bkm_freeEnergy_rate_nonpos
  simp

end InfoGeometry.Canonical.EntrywiseBKMOnsagerMobility
