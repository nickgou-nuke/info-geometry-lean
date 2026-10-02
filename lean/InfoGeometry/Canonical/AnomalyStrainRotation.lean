import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Canonical.SquareZeroStrainRotation

/-!
# The actual Einstein anomaly and the actual fluid strain/rotation owners

The Moore–Penrose range identity makes the existing Einstein anomaly
square-zero. Its strain and rotation therefore have opposite squares and
anticommute. These statements assert no time evolution or PDE regularity.
-/

namespace InfoGeometry.Canonical.AnomalyStrainRotation

section Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- The existing anomaly factors through the complementary range sector. -/
theorem anomaly_factorization
    (a b c : A) (h : IsMoorePenroseInverse a b) :
    EinsteinAnomaly a b c = (a * c) * (1 - a * b) := by
  exact SquareZeroStrainRotation.commutator_factorization a b c h

/-- The actual Einstein anomaly is square-zero under the Moore–Penrose laws. -/
theorem anomaly_mul_self_eq_zero
    (a b c : A) (h : IsMoorePenroseInverse a b) :
    EinsteinAnomaly a b c * EinsteinAnomaly a b c = 0 := by
  exact SquareZeroStrainRotation.commutator_mul_self_eq_zero a b c h

/-- Self-adjoint regularization forces this particular anomaly to vanish. -/
theorem anomaly_eq_zero_of_regularization_selfAdjoint
    (a b c : A) (h : IsMoorePenroseInverse a b)
    (hc : star (a * c) = a * c) :
    EinsteinAnomaly a b c = 0 := by
  exact SquareZeroStrainRotation.commutator_eq_zero_of_regularization_selfAdjoint a b c h hc

end Ring

section Hilbert

variable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The existing fluid strain and rotation inherit the exact nilpotent identities. -/
theorem anomaly_strain_rotation
    (a b c : VelocityField E) (h : IsMoorePenroseInverse a b) :
    strainRate (EinsteinAnomaly a b c) * strainRate (EinsteinAnomaly a b c) =
        -(vorticity (EinsteinAnomaly a b c) * vorticity (EinsteinAnomaly a b c)) ∧
    strainRate (EinsteinAnomaly a b c) * vorticity (EinsteinAnomaly a b c) =
        -(vorticity (EinsteinAnomaly a b c) * strainRate (EinsteinAnomaly a b c)) := by
  simpa only [strainRate, vorticity] using
    SquareZeroStrainRotation.square_zero_scaled_star_pair (EinsteinAnomaly a b c)
      (anomaly_mul_self_eq_zero a b c h) ((2 : ℝ)⁻¹)

end Hilbert

end InfoGeometry.Canonical.AnomalyStrainRotation
