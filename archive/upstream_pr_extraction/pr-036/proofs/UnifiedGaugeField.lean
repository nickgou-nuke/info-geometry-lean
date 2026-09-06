import Mathlib
import proofs.EinsteinThermodynamicBridge

/-!
# Unified gauge-field accounting

This file proves the finite scalar accounting identity used by the thermodynamic
unification story: if total energy is vacuum/Fisher energy plus gauge curvature,
subtracting the gauge term recovers the vacuum source.
-/

noncomputable section

namespace UnifiedGaugeField

open InformationGeometricCutoff
open EinsteinThermodynamicBridge



/-- Scalar unified field accounting over the Fisher/Cramér--Rao source. -/
structure UnifiedFieldScalar (cr : CramerRaoQuantumInequality) where
  fisherSpacetime : FisherSpacetime cr
  gaugeCurvature : ℝ
  totalEnergyDensity : ℝ
  total_energy_eq : totalEnergyDensity = cr.phaseSpaceVariance + gaugeCurvature

/-- Removing the gauge-curvature contribution from the total energy recovers the
Cramér--Rao/Fisher vacuum source. -/
theorem total_energy_minus_gauge
    (cr : CramerRaoQuantumInequality) (u : UnifiedFieldScalar cr) :
    u.totalEnergyDensity - u.gaugeCurvature = cr.phaseSpaceVariance := by
  rw [u.total_energy_eq]
  ring

/-- If the scalar Einstein equation uses the Fisher source, the unified scalar
energy accounting is compatible with the curvature side after subtracting the
gauge-curvature contribution. -/
theorem gravity_gauge_scalar_accounting
    (cr : CramerRaoQuantumInequality) (u : UnifiedFieldScalar cr)
    (einstein : EinsteinThermodynamicEquation u.fisherSpacetime) :
    u.fisherSpacetime.ricciScalar / 2 + u.fisherSpacetime.lambda =
      u.totalEnergyDensity - u.gaugeCurvature := by
  rw [total_energy_minus_gauge]
  rw [einstein.equation]
  exact u.fisherSpacetime.energy_density_eq



end UnifiedGaugeField
