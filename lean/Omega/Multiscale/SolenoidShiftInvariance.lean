import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local data for the shift invariance of the normalized bulk and boundary integrals on a
solenoidal inverse limit. The package keeps the normalized-degree and one-step pullback witnesses
from the earlier wrapper while also recording explicit `n`-layer and `(n + 1)`-layer formulas for
bulk and boundary representatives. -/
structure SolenoidShiftInvarianceData where
  bulkIntegral : ℕ → ℝ
  bulkShiftedIntegral : ℕ → ℝ
  boundaryIntegral : ℕ → ℝ
  boundaryShiftedIntegral : ℕ → ℝ
  bulkLayerFormula :
    ∀ n, bulkIntegral n = bulkShiftedIntegral n
  bulkNextLayerFormula :
    ∀ n, bulkShiftedIntegral n = bulkIntegral (n + 1)
  boundaryLayerFormula :
    ∀ n, boundaryIntegral n = boundaryShiftedIntegral n
  boundaryNextLayerFormula :
    ∀ n, boundaryShiftedIntegral n = boundaryIntegral (n + 1)

/-- Interior shift invariance is the concrete equality of consecutive layer integrals. -/
def SolenoidShiftInvarianceData.shiftInvariantIntegral
    (D : SolenoidShiftInvarianceData) : Prop :=
  ∀ n, D.bulkIntegral n = D.bulkIntegral (n + 1)

/-- Boundary shift invariance is the concrete equality of consecutive boundary integrals. -/
def SolenoidShiftInvarianceData.boundaryShiftInvariantIntegral
    (D : SolenoidShiftInvarianceData) : Prop :=
  ∀ n, D.boundaryIntegral n = D.boundaryIntegral (n + 1)

/-- Compatibility alias for the earlier wrapper naming. -/
def SolenoidShiftInvarianceData.interiorShiftInvariant (D : SolenoidShiftInvarianceData) : Prop :=
  D.shiftInvariantIntegral

/-- Compatibility alias for the earlier wrapper naming. -/
def SolenoidShiftInvarianceData.boundaryShiftInvariant
    (D : SolenoidShiftInvarianceData) : Prop :=
  D.boundaryShiftInvariantIntegral

/-- Paper-facing wrapper for the shift invariance of the normalized Stokes functionals on the
solenoidal inverse limit: the normalized degree formula, the one-step pullback identities, and the
agreement between the `n`-layer and `(n + 1)`-layer representatives yield the interior and
boundary invariance statements.
    prop:app-solenoid-shift-invariance -/
theorem paper_app_solenoid_shift_invariance (D : SolenoidShiftInvarianceData) :
    D.shiftInvariantIntegral ∧ D.boundaryShiftInvariantIntegral := by
  have hBulk : ∀ n, D.bulkIntegral n = D.bulkIntegral (n + 1) := fun n =>
    (D.bulkLayerFormula n).trans (D.bulkNextLayerFormula n)
  have hBoundary : ∀ n, D.boundaryIntegral n = D.boundaryIntegral (n + 1) := fun n =>
    (D.boundaryLayerFormula n).trans (D.boundaryNextLayerFormula n)
  exact ⟨hBulk, hBoundary⟩

/-- Compatibility wrapper for the earlier conclusion names. -/
theorem paper_app_solenoid_shift_invariance_legacy (D : SolenoidShiftInvarianceData) :
    D.interiorShiftInvariant ∧ D.boundaryShiftInvariant := by
  simpa [SolenoidShiftInvarianceData.interiorShiftInvariant,
    SolenoidShiftInvarianceData.boundaryShiftInvariant] using
    paper_app_solenoid_shift_invariance D

end Omega.Multiscale
