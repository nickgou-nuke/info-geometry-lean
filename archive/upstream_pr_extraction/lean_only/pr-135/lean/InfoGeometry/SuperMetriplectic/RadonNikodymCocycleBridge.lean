import InfoGeometry.Canonical.RelativeSurprisalRadonNikodymBridge

/-!
# Retired scalar Radon--Nikodym readout

The former `HKState`/`ℝ` implementation was only a transverse quadratic
readout.  It was not a Radon--Nikodym derivative, a modular cocycle, or an
Onsager bracket, so it is intentionally no longer exported as theorem API.

The maintained noncommutative owners are:

* `RelativeModularOperator.relativeModularOperator` for the finite relative
  modular operator;
* `RelativeSurprisalOperatorLift.relativeModularPotentialOperator` for its
  first-quantized negative-log potential;
* `RelativeSurprisalRadonNikodym.relativeSurprisalOperator_diag` for the
  diagonal readout.

This compatibility module therefore exports no scalar surrogate and makes no
claim about a general measure-theoretic or type-III Radon--Nikodym theorem.
-/

namespace InfoGeometry.SuperMetriplectic.TransverseCocycleReadout

end InfoGeometry.SuperMetriplectic.TransverseCocycleReadout
