import InfoGeometry.Routing.DiscreteRoPERepresentation
import InfoGeometry.OperatorAlgebra.CliffordRoPETorus
import InfoGeometry.Clifford.DiscreteMoebiusGroup
import InfoGeometry.Clifford.ModularCftBridge
import InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

/-! Bridge between the integer positional character, its continuous rotor, and
the native elliptic Clifford generator. -/

noncomputable section

namespace InfoGeometry.Canonical.PositionalEncodingCharacterBridge

open InfoGeometry.Routing.PlanarRotation
open InfoGeometry.Routing.DiscreteRoPERepresentation
open InfoGeometry.OperatorAlgebra.CliffordRoPETorus
open InfoGeometry.Clifford.DiscreteMoebiusGroup
open InfoGeometry.Clifford.ModularCftBridge
open InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

theorem ropeRotor_eq_ellipticRotor (θ : ℝ) (m : ℤ) :
    ropeRotor θ m = ellipticRotor θ (m : ℝ) := by
  rfl

theorem ropeRotor_add_as_continuous_character (θ : ℝ) (m n : ℤ) :
    ellipticRotor θ ((m + n : ℤ) : ℝ) =
      ellipticRotor θ (m : ℝ) * ellipticRotor θ (n : ℝ) := by
  rw [← ropeRotor_eq_ellipticRotor θ (m + n)]
  rw [ropeRotor_add]
  rw [ropeRotor_eq_ellipticRotor, ropeRotor_eq_ellipticRotor]

theorem ellipticRotor_as_clifford_generator (θ t : ℝ) :
    ellipticRotor θ t =
      Real.cos (t * θ) • (1 : Mat2) +
        Real.sin (t * θ) • ellipticGenerator := by
  unfold ellipticRotor
  exact rotation_as_elliptic_generator (t * θ)

theorem ellipticRotor_relative_as_group_character (θ s t : ℝ) :
    Matrix.transpose (ellipticRotor θ s) * ellipticRotor θ t =
      ellipticRotor θ (t - s) := by
  exact ellipticRotor_relative θ s t

/-! The already-defined modular Möbius translation is also an additive
positional representation.  This is only an interface bridge: the Möbius
action and the modular generator remain owned by their Clifford modules. -/

noncomputable def modularMoebiusPositionRepresentation :
    AdditivePositionRepresentation (ℂ → ℂ) ℕ where
  unit := id
  mul := fun f g => g ∘ f
  value := fun m z => moebiusAction (modularT ^ m) z
  value_zero := by
    funext z
    simp [moebiusAction, modularT]
  value_add := by
    intro m n
    funext z
    rw [modularT_pow]
    simp [moebiusAction, modularT_pow]
    ring

theorem modularMoebiusPositionRepresentation_value (m : ℕ) (z : ℂ) :
    modularMoebiusPositionRepresentation.value m z = z + (m : ℂ) := by
  simp [modularMoebiusPositionRepresentation, moebiusAction, modularT_pow]

end InfoGeometry.Canonical.PositionalEncodingCharacterBridge
