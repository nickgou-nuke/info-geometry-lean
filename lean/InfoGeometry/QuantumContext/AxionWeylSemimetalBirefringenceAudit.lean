/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AxionWeylSemimetalBirefringence

/-!
# Concrete Integer Instantiation & Audit for Section 118: Axion Weyl Semimetal Birefringence
Target: `InfoGeometry/QuantumContext/AxionWeylSemimetalBirefringenceAudit.lean`

Verifies over `ℤ` (`decide`) and via `#print axioms` that `totalAxionCurrent`,
`anomalousHallCurrent`, `axionGaugeTerm`, and `chiral_tachyonic_zitterbewegung_instability`
evaluate to exact non-trivial values.
-/

namespace InfoGeometry.QuantumContext.AxionBirefringenceAudit

open InfoGeometry.QuantumContext.AxionBirefringence

/-- Concrete verification of `totalAxionCurrent`, `anomalous_hall_zero_joule_heating`,
and `axion_current_power_is_pontryagin` over `ℤ`. -/
theorem sample_axion_current_power_int :
    let b_vec : Vec3 ℤ := ⟨1, -2, 3⟩
    let E : Vec3 ℤ := ⟨2, 3, 1⟩
    let B : Vec3 ℤ := ⟨4, 1, 2⟩
    Vec3.dot E (anomalousHallCurrent b_vec E) = 0 ∧
    pontryaginInvariant E B = 13 ∧
    Vec3.dot E (totalAxionCurrent 5 b_vec E B) = 65 ∧
    axionGaugeTerm 5 E B = 65 := by
  decide

/-- Concrete verification of subcritical tachyonic instability (`k = 2, b₀ = 5 ⟹ Ω₊ Ω₋ = -21 < 0`). -/
theorem sample_subcritical_tachyonic_instability_int :
    omegaRight (2 : ℤ) 5 = 7 ∧
    omegaLeft (2 : ℤ) 5 = -3 ∧
    omegaRight (2 : ℤ) 5 * omegaLeft (2 : ℤ) 5 = -21 ∧
    (-21 : ℤ) < 0 := by
  decide

#print axioms InfoGeometry.QuantumContext.AxionBirefringence.Vec3.unitY_ne_zero
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.Vec3.dot_cross_self_right
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.Vec3.cross_noncommutative_int
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.poynting_fujikawa_lagrange_identity
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.anomalous_hall_zero_joule_heating
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.axion_current_power_is_pontryagin
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.phase_velocity_birefringence_splitting
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.chiral_tachyonic_zitterbewegung_instability
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.destructive_birefringence_negative_dwell_time
#print axioms InfoGeometry.QuantumContext.AxionBirefringence.axion_weyl_birefringence_master_synthesis

end InfoGeometry.QuantumContext.AxionBirefringenceAudit
