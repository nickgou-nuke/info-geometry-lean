import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.CartanWeylBogoliubovGravity

/-!
# Gravity soldering finite aliases

Finite component consequences of the Pauli soldering metric.
-/

noncomputable section

namespace GravitySoldering

open Matrix

/-- Reuse the active Pauli soldering metric component. -/
def metric_components (i j : Fin 4) : ℂ :=
  (1 / 4 : ℂ) * CartanWeylBogoliubovGravity.tr2C
    (CartanWeylBogoliubovGravity.σ i * CartanWeylBogoliubovGravity.σbar j +
     CartanWeylBogoliubovGravity.σ j * CartanWeylBogoliubovGravity.σbar i)

/-- The time-time soldered metric component is `+1`. -/
theorem diagonal_component_zero : metric_components 0 0 = 1 := by
  simpa [metric_components, CartanWeylBogoliubovGravity.etaSign] using
    CartanWeylBogoliubovGravity.pauli_solder_metric 0 0

/-- The first spatial soldered metric component is `-1`. -/
theorem diagonal_component_one : metric_components 1 1 = -1 := by
  simpa [metric_components, CartanWeylBogoliubovGravity.etaSign] using
    CartanWeylBogoliubovGravity.pauli_solder_metric 1 1

/-- Off-diagonal time/space soldered metric component vanishes. -/
theorem off_diagonal_component_zero_one : metric_components 0 1 = 0 := by
  simpa [metric_components, CartanWeylBogoliubovGravity.etaSign] using
    CartanWeylBogoliubovGravity.pauli_solder_metric 0 1

/-- Three finite Pauli soldering metric components. -/
theorem finite_pauli_soldering :
    metric_components 0 0 = 1 ∧ metric_components 1 1 = -1 ∧
      metric_components 0 1 = 0 := by
  constructor
  · exact diagonal_component_zero
  constructor
  · exact diagonal_component_one
  · exact off_diagonal_component_zero_one

end GravitySoldering
