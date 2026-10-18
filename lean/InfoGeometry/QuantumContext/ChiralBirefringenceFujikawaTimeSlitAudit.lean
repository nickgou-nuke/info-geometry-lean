/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.ChiralBirefringenceFujikawaTimeSlit

/-!
# Concrete Integer Instantiation & Audit for Section 117a: Fujikawa Chiral Anomaly & Time-Slit Birefringence
Target: `InfoGeometry/QuantumContext/ChiralBirefringenceFujikawaTimeSlitAudit.lean`

Verifies over `ℤ` (`decide`) and via `#print axioms` that all declarations in
`InfoGeometry.QuantumContext.FujikawaBirefringence` are non-vacuous and axiom-free.
-/

namespace InfoGeometry.QuantumContext.FujikawaBirefringenceAudit

open InfoGeometry.QuantumContext.FujikawaBirefringence

/-- Concrete verification of `fujikawa_anomaly_factor_two` and `poynting_fujikawa_energy_partition` over `ℤ`. -/
theorem sample_fujikawa_and_poynting_partition_int :
    let M : ChiralZeroModes ℤ := ⟨5, 2⟩
    let E : Vec3 ℤ := ⟨1, 2, 2⟩
    let B : Vec3 ℤ := ⟨2, 1, 2⟩
    atiyahSingerIndex M = 3 ∧
    fujikawaMeasureExponent 4 M = -24 ∧
    poyntingSq E B = 17 ∧
    pontryaginSource E B = 8 ∧
    poyntingSq E B + (pontryaginSource E B) ^ 2 = 81 ∧
    Vec3.sq E * Vec3.sq B = 81 := by
  decide

/-- Concrete verification of `chiral_birefringence_frequency_split` and `chiral_eikonal_dispersion_product` over `ℤ`. -/
theorem sample_chiral_birefringence_eikonal_int :
    eikonalOmegaPlus (7 : ℤ) 3 = 10 ∧
    eikonalOmegaMinus (7 : ℤ) 3 = 4 ∧
    eikonalOmegaPlus (7 : ℤ) 3 - eikonalOmegaMinus (7 : ℤ) 3 = 6 ∧
    eikonalOmegaPlus (7 : ℤ) 3 * eikonalOmegaMinus (7 : ℤ) 3 = 40 ∧
    (7 : ℤ) ^ 2 - (3 : ℤ) ^ 2 = 40 := by
  decide

#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.Vec3.unitX_ne_zero
#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.Vec3.cross_noncommutative_int
#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.ChiralZeroModes.unitRightMode_ne_zero
#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.fujikawa_anomaly_factor_two
#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.poynting_fujikawa_energy_partition
#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.chiral_birefringence_frequency_split
#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.chiral_eikonal_dispersion_product
#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.steinberg_negative_dwell_time_from_positive_delays
#print axioms InfoGeometry.QuantumContext.FujikawaBirefringence.fujikawa_birefringence_master_synthesis

end InfoGeometry.QuantumContext.FujikawaBirefringenceAudit
