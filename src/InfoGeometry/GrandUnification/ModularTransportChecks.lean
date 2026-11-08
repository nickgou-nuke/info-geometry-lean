/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.GrandUnification.ModularTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GrandUnification.SpectralThermalNormalization

/-!
# Checks — Modular Transport Cocycle & Souriau–Tomita Synthesis

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.GrandUnification.ModularTransport`,
    `InfoGeometry.GrandUnification.SpectralThermalNormalization`.
- BUCKET 2 (Deconfabulation):
  * Signature verification for the wrapper-free modular transport and
    spectral thermal normalization theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `#check` verification module.
-/

namespace InfoGeometry.GrandUnification.Checks

#check InfoGeometry.GrandUnification.finite_modular_connes_phase_cocycle_law
#check InfoGeometry.GrandUnification.tomita_gromov_finite_connes_souriau_synthesis
#check InfoGeometry.GrandUnification.spectralThermalNormalization_partition_pos
#check InfoGeometry.GrandUnification.spectralThermalNormalization_partitionPotential_eq_logZ
#check InfoGeometry.GrandUnification.spectralThermalNormalization_negativeLogGibbsDensity
#check InfoGeometry.GrandUnification.spectralThermalNormalization_statewise_log_generator

end InfoGeometry.GrandUnification.Checks
