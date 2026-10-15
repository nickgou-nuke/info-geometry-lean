/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornGaugeEmergence

/-!
# Audit Companion: Noncommutative Zorn Peirce Idempotents and Gauge Subalgebra Emergence

This file audits the axiomatic footprint of all theorems in
`InfoGeometry.Algebra.ZornGaugeEmergence`.
-/

namespace InfoGeometry.Algebra.ZornGaugeEmergence.Audit

open InfoGeometry.Algebra.ZornGaugeEmergence

#print axioms vacuumP1_sq
#print axioms vacuumP2_sq
#print axioms vacuumP1_mul_vacuumP2
#print axioms vacuumP2_mul_vacuumP1
#print axioms vacuumP1_add_vacuumP2
#print axioms vacuumP1_mul
#print axioms vacuumP2_mul
#print axioms peirce_11
#print axioms peirce_12
#print axioms peirce_21
#print axioms peirce_22
#print axioms zorn_peirce_decomposition

#print axioms stabilizes_vacuum_iff_P2
#print axioms derivation_preserves_color_triplet
#print axioms derivation_preserves_color_antitriplet
#print axioms derivation_preserves_vacuum_p1_block
#print axioms derivation_preserves_vacuum_p2_block

#print axioms triplet_mul_triplet
#print axioms triplet_mul_antitriplet

#print axioms tripotentGrading_sq
#print axioms tripotentGrading_cube
#print axioms tripotentGrading_annihilates_P1
#print axioms tripotentGrading_annihilates_P2
#print axioms tripotentGrading_on_triplet
#print axioms tripotentGrading_on_antitriplet

#print axioms zorn_gauge_emergence_synthesis

open InfoGeometry.Physics.NoncommutativeZornBdGDerivations

/-- The grading kernel consists exactly of diagonal coefficient pairs. This checks
both off-diagonal sectors; it does not claim anything about compiler axioms. -/
theorem tripotentGrading_eq_zero_iff {A : Type*} [Ring A] (X : NCZorn A) :
    tripotentGrading X = 0 ↔ X.u = 0 ∧ X.v = 0 := by
  constructor
  · intro h
    constructor
    · exact congrArg NCZorn.u h
    · have hv := congrArg NCZorn.v h
      funext i
      have hi := congrFun hv i
      change -X.v i = 0 at hi
      exact neg_eq_zero.mp hi
  · rintro ⟨hu, hv⟩
    apply NCZorn.ext
    · rfl
    · change X.u = (fun _ => 0)
      exact hu
    · funext i
      change -X.v i = 0
      simp [hv]
    · rfl

#print axioms tripotentGrading_eq_zero_iff

end InfoGeometry.Algebra.ZornGaugeEmergence.Audit
