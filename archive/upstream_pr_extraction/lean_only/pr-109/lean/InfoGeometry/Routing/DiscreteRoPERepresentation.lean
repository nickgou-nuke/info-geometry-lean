import InfoGeometry.Routing.PlanarRotation

/-! A discrete RoPE representation on the verified planar rotation carrier.

This owner proves the additive-position laws only.  It does not identify the
carrier with a Clifford module or with KZ parallel transport.
-/

namespace InfoGeometry.Routing.DiscreteRoPERepresentation

open InfoGeometry.Routing.PlanarRotation

noncomputable def ropeRotor (θ : ℝ) (m : ℤ) : Mat2 :=
  rotation ((m : ℝ) * θ)

theorem ropeRotor_zero (θ : ℝ) : ropeRotor θ 0 = (1 : Mat2) := by
  unfold ropeRotor
  simp [rotation_zero]

theorem ropeRotor_add (θ : ℝ) (m n : ℤ) :
    ropeRotor θ (m + n) = ropeRotor θ m * ropeRotor θ n := by
  unfold ropeRotor
  rw [Int.cast_add, add_mul, rotation_mul_rotation]

theorem ropeRotor_inverse (θ : ℝ) (m : ℤ) :
    ropeRotor θ m * ropeRotor θ (-m) = (1 : Mat2) := by
  unfold ropeRotor
  rw [rotation_mul_rotation]
  push_cast
  rw [show (m : ℝ) * θ + (-↑m) * θ = 0 by ring, rotation_zero]

theorem ropeRotor_relative (θ : ℝ) (m n : ℤ) :
    ropeRotor θ (-m) * ropeRotor θ n = ropeRotor θ (n - m) := by
  unfold ropeRotor
  rw [rotation_mul_rotation]
  congr 1
  push_cast
  ring

end InfoGeometry.Routing.DiscreteRoPERepresentation
