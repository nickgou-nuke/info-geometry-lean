import InfoGeometry.Routing.PlanarRotation

/-! The one-plane elliptic Clifford/RoPE interface.

The carrier is the explicit real two-dimensional matrix plane.  The file does
not claim a multi-plane Clifford torus or a KZ comparison.
-/

namespace InfoGeometry.OperatorAlgebra.CliffordRoPETorus

open InfoGeometry.Routing.PlanarRotation

noncomputable def ellipticRotor (theta t : ℝ) : Mat2 :=
  rotation (t * theta)

theorem ellipticRotor_zero (theta : ℝ) :
    ellipticRotor theta 0 = (1 : Mat2) := by
  unfold ellipticRotor
  simp [rotation_zero]

theorem ellipticRotor_add (theta s t : ℝ) :
    ellipticRotor theta (s + t) =
      ellipticRotor theta s * ellipticRotor theta t := by
  unfold ellipticRotor
  rw [add_mul, rotation_mul_rotation]

theorem ellipticRotor_inverse (theta t : ℝ) :
    ellipticRotor theta t * ellipticRotor theta (-t) = (1 : Mat2) := by
  unfold ellipticRotor
  rw [rotation_mul_rotation]
  rw [show t * theta + (-t) * theta = 0 by ring, rotation_zero]

theorem ellipticRotor_relative (theta m n : ℝ) :
    Matrix.transpose (ellipticRotor theta m) * ellipticRotor theta n =
      ellipticRotor theta (n - m) := by
  unfold ellipticRotor
  rw [rotation_transpose, rotation_mul_rotation]
  congr 1
  ring

/-! The split/hyperbolic counterpart, using the already verified boost plane. -/

noncomputable def hyperbolicRotor (theta t : ℝ) : Mat2 :=
  splitRotation (t * theta)

theorem hyperbolicRotor_zero (theta : ℝ) :
    hyperbolicRotor theta 0 = (1 : Mat2) := by
  unfold hyperbolicRotor
  simp [splitRotation_zero]

theorem hyperbolicRotor_add (theta s t : ℝ) :
    hyperbolicRotor theta (s + t) =
      hyperbolicRotor theta s * hyperbolicRotor theta t := by
  unfold hyperbolicRotor
  rw [add_mul, splitRotation_mul_splitRotation]

theorem hyperbolicRotor_inverse (theta t : ℝ) :
    hyperbolicRotor theta t * hyperbolicRotor theta (-t) = (1 : Mat2) := by
  unfold hyperbolicRotor
  rw [splitRotation_mul_splitRotation]
  rw [show t * theta + (-t) * theta = 0 by ring, splitRotation_zero]

theorem hyperbolicRotor_relative (theta m n : ℝ) :
    hyperbolicRotor theta m * hyperbolicRotor theta n =
      hyperbolicRotor theta (m + n) := by
  exact (hyperbolicRotor_add theta m n).symm

theorem hyperbolicRotor_relative_displacement (theta m n : ℝ) :
    hyperbolicRotor theta (-m) * hyperbolicRotor theta n =
      hyperbolicRotor theta (n - m) := by
  calc
    hyperbolicRotor theta (-m) * hyperbolicRotor theta n =
        hyperbolicRotor theta ((-m) + n) :=
      (hyperbolicRotor_add theta (-m) n).symm
    _ = hyperbolicRotor theta (n - m) := by
      congr 1
      ring

end InfoGeometry.OperatorAlgebra.CliffordRoPETorus
