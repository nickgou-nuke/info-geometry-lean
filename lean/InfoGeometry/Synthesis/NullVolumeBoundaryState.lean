/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Cosmology.CustodialTwinWittBridge
import InfoGeometry.Physics.DeBroglieSpinorFusionMaxwell
import InfoGeometry.Tomita.FiniteTomitaModularFlow

/-!
# Null-volume boundary state

This synthesis packages the repaired finite owners without adding an analytic
or physical identification that they do not prove.  The data consists of the
canonical doubled Witt boundary, the sewn `Cl(1,1)` boundary carrier, and the
canonical sewn state; the finite phase complex square, custodial involution,
and sewn-state fixpoint are proved as theorems from their exact owner results.
The remaining boundary anomaly and null-quadric statements retain their
explicit operator/matrix hypotheses.
-/

noncomputable section

open InfoGeometry.Krein
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
open InfoGeometry.Cosmology.CustodialTwinWittBridge
open InfoGeometry.Physics.DeBroglieSpinorFusionMaxwell
open InfoGeometry.Tomita.FiniteTomitaModularFlow
open InfoGeometry.OperatorAlgebra.PeirceBiSandwich
open InfoGeometry.Lie.SO55GlobalConformalPrecursors

namespace InfoGeometry.Synthesis.NullVolumeBoundaryState

/-- The exact finite data currently represented by the null boundary lane. -/
structure Data where
  witt : WittDecomposition
  cl11 : FiniteCl11 ℝ
  sewnState : H_lp ℝ

/-- Canonical construction from the repaired owner modules. -/
def canonical : Data where
  witt := canonicalWittDecomposition
  cl11 := canonicalCl11 (E := ℝ)
  sewnState := canonicalCantorSewnState

/-- The canonical finite phase complex structure squares to minus the identity. -/
theorem canonical_phase_complex_square :
    (J_phase2 : Matrix (Fin 2) (Fin 2) ℝ) * J_phase2 = -I2_R := by
  exact InfoGeometry.OperatorAlgebra.PeirceBiSandwich.J_phase2_sq

/-- The canonical custodial twin operator is an involution. -/
theorem canonical_custodial_involution :
    W_twin16 * W_twin16 = 1 := by
  exact (InfoGeometry.OperatorAlgebra.PeirceBiSandwich.custodial_boost_comm_even_powers 0).1

/-- The canonical sewn boundary state is fixed by the modular swap. -/
theorem canonical_sewn_state_fixed :
    J_lp_clm (E := ℝ) canonical.sewnState = canonical.sewnState := by
  exact canonicalCantorSewnState_fixed

/-- The canonical package contains complementary isotropic Witt sectors. -/
theorem canonical_witt_direct_sum :
    canonical.witt.W_plus ⊔ canonical.witt.W_minus =
      (⊤ : Submodule ℝ (Fin 10 → ℝ)) := by
  exact canonical.witt.h_direct_sum

/-- The canonical sewn state cancels every explicitly sewn chiral observable. -/
theorem canonical_anomaly_cancellation
    (B : H_lp ℝ →L[ℝ] H_lp ℝ)
    (hB : (J_lp_clm (E := ℝ)).comp
      (B.comp (J_lp_clm (E := ℝ))) = B) :
    inner ℝ canonical.sewnState
      (((epsilon_lp_clm (E := ℝ)).comp B) canonical.sewnState) = 0 := by
  simpa [canonical] using canonical_state_chiral_zero B hB

/-- Every explicit `SO(5,5)` boost transports null boundary vectors to null
boundary vectors. -/
theorem boost_preserves_null_boundary
    (ξ : ℝ) {x : Fin 10 → ℝ} (hx : x ∈ NullQuadric) :
    (so55Boost ξ).mulVec x ∈ NullQuadric := by
  exact null_quadric_invariant (so55Boost ξ) (so55_boost_preserves_witt_structure ξ) hx

end InfoGeometry.Synthesis.NullVolumeBoundaryState
