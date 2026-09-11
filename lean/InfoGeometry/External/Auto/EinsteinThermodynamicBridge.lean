import InfoGeometry.External.Auto.InformationGeometricCutoff
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Conditional scalar positivity from the Cramér–Rao cutoff

This module records a scalar implication: if a source scalar is
identified with the positive Cramér–Rao phase-space variance, and another scalar
expression is assumed equal to that source, then the expression is positive.
-/

noncomputable section

namespace EinsteinThermodynamicBridge

open InformationGeometricCutoff

/-- Positivity transports from the Cramér–Rao variance through explicit source
identification and scalar balance hypotheses. -/
theorem positive_scalar_source_side
    (cr : CramerRaoQuantumInequality)
    (ricciScalar lambda energyDensity : ℝ)
    (henergy : energyDensity = cr.phaseSpaceVariance)
    (hbalance : ricciScalar / 2 + lambda = energyDensity) :
    0 < ricciScalar / 2 + lambda := by
  have hcr : 0 < cr.phaseSpaceVariance := fractal_resolution_limit cr
  rw [hbalance, henergy]
  exact hcr

/-- The same implication specialized to the finite Penrose scale used by the
cutoff owner.  This remains conditional on the supplied scalar balance. -/
theorem penrose_scale_scalar_source_positive
    (cr : CramerRaoQuantumInequality)
    (ricciScalar energyDensity : ℝ)
    (henergy : energyDensity = cr.phaseSpaceVariance)
    (hbalance : ricciScalar / 2 + penroseBeta ^ 2 = energyDensity) :
    0 < ricciScalar / 2 + penroseBeta ^ 2 :=
  positive_scalar_source_side cr ricciScalar (penroseBeta ^ 2) energyDensity
    henergy hbalance

end EinsteinThermodynamicBridge

end noncomputable section
