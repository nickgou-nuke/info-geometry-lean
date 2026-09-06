import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-!
# Spatial state and Cantor cylinder mass

This consumer identifies the constant-vector state on the concrete boundary
Hilbert space with Bernoulli cylinder mass on the operator projection tree.
It is deliberately a spatial-state theorem; it does not identify this state
with the distinct gauge-invariant word kernel on off-diagonal monomials.
-/

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCylinderStateBridge

open MeasureTheory
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderProjectionBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

theorem spatialState_operatorCylinderProjection_word (w : List Bool) :
    spatialState.functional (operatorCylinderProjection w) =
      ((μC (wordBranchSet w)).toReal : ℂ) := by
  classical
  rw [spatialState_apply]
  dsimp [cantorVacuumState]
  rw [L2.inner_def]
  have hvac := vacuumL2_coeFn
  have hproj := operatorCylinderProjection_coeFn w vacuumL2
  have hint :
      (fun x => inner ℂ ((vacuumL2 : Boundary → ℂ) x)
        (((operatorCylinderProjection w vacuumL2 : L2Boundary) : Boundary → ℂ) x)) =ᵐ[μC]
        (wordBranchSet w).indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [hvac, hproj] with x hx hpx
    rw [hx, hpx]
    by_cases h : x ∈ wordBranchSet w
    · simpa [Set.indicator_of_mem h] using hx
    · rw [Set.indicator_apply, if_neg h, Set.indicator_apply, if_neg h]
      simp
  rw [integral_congr_ae hint]
  rw [integral_indicator (measurableSet_wordBranchSet w)]
  rw [integral_const]
  have hmeasure :
      (μC.restrict (wordBranchSet w)).real Set.univ =
        (μC (wordBranchSet w)).toReal := by
    dsimp [Measure.real]
    rw [Measure.restrict_apply_univ]
  rw [hmeasure]
  simp

theorem spatialState_operatorCylinderProjection_word_eq_bernoulli
    (w : List Bool) :
    spatialState.functional (operatorCylinderProjection w) =
      ((1 / 2 : ℝ≥0∞) ^ w.length).toReal := by
  rw [spatialState_operatorCylinderProjection_word, μC_wordBranchSet]

/-! The two states have the same diagonal cylinder marginal.  This does not
identify their values on off-diagonal Cuntz word monomials. -/

theorem spatialState_eq_canonicalGaugeState_on_projection
    (w : List Bool) :
    spatialState.functional (operatorCylinderProjection w) =
      canonicalGaugeState w w := by
  rw [spatialState_operatorCylinderProjection_word]
  symm
  exact canonicalGaugeState_word_eq_wordBranchSet_measure_toReal w

end InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCylinderStateBridge
