import InfoGeometry.SuperMetriplectic.Flow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge
import InfoGeometry.Canonical.MetriplecticJacobianDecompositionBridge
import InfoGeometry.Canonical.RelativeSurprisalJacobianCocycleBridge

/-!
# Compatibility surface for native metriplectic dissipation

The retired scalar `u^2 * Q` readout did not define a flow, a state, or a
Jacobian.  Use `MetriplecticFlow`, positive-functional Fisher/BKM readouts,
and the log-Jacobian cocycle for theorem-bearing statements.
-/

namespace InfoGeometry.Topology.ZetaMetriplecticOnsagerFactorizationBridge

open InfoGeometry.SuperMetriplectic
open InfoGeometry.Canonical.MetriplecticJacobianDecomposition

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-!
The following theorems are the native compatibility surface.  They package
the already-proved body-level `MetriplecticFlow` facts; no identification with
the scalar Jacobian model or with an analytic zeta flow is made here.
-/

theorem entropyProduction_eq_native_onsager_quadratic
    (F : MetriplecticFlow V) :
    F.entropyProduction = F.metric.quadratic F.entropyForce := by
  simpa [OnsagerMetricData.quadratic] using
    F.entropyProduction_eq_onsager_quadratic

theorem dissipativeFlow_eq_native_onsager_entropy
    (F : MetriplecticFlow V) :
    F.dissipativeFlow = F.metric.onsager F.entropyForce :=
  F.dissipativeFlow_eq_onsager_entropy

theorem native_metriplectic_second_law_and_energy_degeneracy
    (F : MetriplecticFlow V) :
    0 ≤ F.entropyProduction ∧
      F.metric.pairing F.energyForce F.dissipativeFlow = 0 := by
  exact ⟨F.entropyProduction_nonnegative,
    F.dissipative_energy_change_eq_zero⟩

theorem native_metriplectic_equilibrium_iff
    (F : MetriplecticFlow V) :
    F.IsDissipativeEquilibrium ↔ F.dissipativeFlow = 0 :=
  F.equilibrium_iff_dissipativeFlow_eq_zero

theorem native_metriplectic_entropyProduction_eq_zero_of_equilibrium
    (F : MetriplecticFlow V)
    (hEq : F.IsDissipativeEquilibrium) :
    F.entropyProduction = 0 := by
  rw [F.entropyProduction_eq_quadratic,
    F.dissipativeFlow_eq_zero_of_equilibrium hEq]
  exact F.metric.pairing_zero_right F.entropyForce

theorem native_metriplectic_totalFlow_eq_reversible_of_equilibrium
    (F : MetriplecticFlow V)
    (hEq : F.IsDissipativeEquilibrium) :
    F.totalFlow = F.reversibleFlow := by
  rw [F.totalFlow_eq_reversible_add_dissipative,
    F.dissipativeFlow_eq_zero_of_equilibrium hEq, add_zero]

end InfoGeometry.Topology.ZetaMetriplecticOnsagerFactorizationBridge
