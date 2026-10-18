/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AharonovTwoStateSphereTime

/-!
# Concrete Integer Instantiation & Axiom Audit for Section 116: Aharonov Two-State Sphere Time
Target: `InfoGeometry/QuantumContext/AharonovTwoStateSphereTimeAudit.lean`

Verifies over `ℤ` (`decide`) the 4D concentric `S³` dilatation scaling, the two-state weak
partition of unity, and the anomalous negative weak dwell time (`W(P̂₁) = -1 < 0`, `W(P̂₂) = 2`).
-/

namespace InfoGeometry.QuantumContext.AharonovTimeAudit

open InfoGeometry.QuantumContext.AharonovTime
open InfoGeometry.QuantumContext.AharonovTime.Sphere4D
open InfoGeometry.QuantumContext.AharonovTime.SlitState2D

/-- Concrete verification over `ℤ` (`decide`) of 4D `S³` radial dilatation scaling
(`radiusSq (dilate 3 ⟨1, 2, 2, 4⟩) = 9 * 25 = 225`) and the anomalous negative weak dwell time
(`normalizedWeakValue1 ⟨1, -2⟩ ⟨1, 1⟩ = -1 < 0`, `normalizedWeakValue2 ⟨1, -2⟩ ⟨1, 1⟩ = 2`). -/
theorem sample_aharonov_sphere_time_int :
    let X : Sphere4D ℤ := ⟨1, 2, 2, 4⟩
    Sphere4D.radiusSq X = 25 ∧
    Sphere4D.radiusSq (Sphere4D.dilate 3 X) = 225 ∧
    SlitState2D.bracket SlitState2D.backwardPostSelected SlitState2D.forwardPreSelected = -1 ∧
    SlitState2D.normalizedWeakValue1 SlitState2D.backwardPostSelected SlitState2D.forwardPreSelected = -1 ∧
    SlitState2D.normalizedWeakValue2 SlitState2D.backwardPostSelected SlitState2D.forwardPreSelected = 2 := by
  decide

#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.unitW_ne_zero
#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.radiusSq_dilate
#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.shell_deviation_expansion
#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.twin_shell_horizon_lock
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit1_idempotent
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit2_idempotent
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit1_projSlit2_zero
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit_partition_of_unity
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.standard_qm_slit1_nonneg
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.standard_qm_slit2_nonneg
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.two_state_weak_partition
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.forwardPreSelected_ne_zero
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.double_slit_registers_negative_weak_time
#print axioms InfoGeometry.QuantumContext.AharonovTime.aharonov_sphere_time_master_synthesis
#print axioms sample_aharonov_sphere_time_int

end InfoGeometry.QuantumContext.AharonovTimeAudit
