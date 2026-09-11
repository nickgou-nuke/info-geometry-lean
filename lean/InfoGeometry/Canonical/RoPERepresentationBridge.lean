import InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Routing.DiscreteRoPERepresentation

namespace InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

open InfoGeometry.Routing.DiscreteRoPERepresentation

noncomputable def ropeRotorRepresentation (θ : ℝ) :
    AdditivePositionRepresentation (Matrix (Fin 2) (Fin 2) ℝ) ℤ where
  unit := 1
  mul := (· * ·)
  value := ropeRotor θ
  value_zero := ropeRotor_zero θ
  value_add := ropeRotor_add θ

theorem ropeRotorRepresentation_relative (θ : ℝ) (m n : ℤ) :
    (ropeRotorRepresentation θ).value (-m) *
        (ropeRotorRepresentation θ).value n =
      (ropeRotorRepresentation θ).value (n - m) := by
  exact ropeRotor_relative θ m n

end InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
