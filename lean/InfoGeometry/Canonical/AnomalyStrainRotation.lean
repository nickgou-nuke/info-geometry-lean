/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Canonical.SquareZeroStrainRotation

/-!
# The actual Einstein anomaly and the actual fluid strain/rotation owners

The Moore–Penrose range identity makes the existing Einstein anomaly
square-zero. Its strain and rotation therefore have opposite squares and
anticommute. These statements assert no time evolution or PDE regularity.

BUCKET 1: The Peirce support, square-zero, and strain/rotation identities below
are proved from the stated Moore–Penrose hypotheses.
BUCKET 2: The ring-level anomaly conclusions are conditional on those
Moore–Penrose laws; the Hilbert-space readout additionally uses the stated
real Hilbert-space structure.
BUCKET 3: No fluid evolution, Navier–Stokes solution, or regularity conclusion
is asserted here.
-/

namespace InfoGeometry.Canonical.AnomalyStrainRotation

section Ring

variable {A : Type*} [Ring A] [StarRing A]

/--
The anomaly has a full one-sided Peirce profile: it factors through the
complementary range sector, is fixed by the range projector on the left,
annihilated by it on the right, and is square-zero.
-/
theorem anomaly_factorization
    (a b c : A) (h : IsMoorePenroseInverse a b) :
    EinsteinAnomaly a b c = (a * c) * (1 - a * b) ∧
    (a * b) * EinsteinAnomaly a b c = EinsteinAnomaly a b c ∧
    EinsteinAnomaly a b c * (a * b) = 0 ∧
    EinsteinAnomaly a b c * EinsteinAnomaly a b c = 0 := by
  have hfactor := SquareZeroStrainRotation.commutator_factorization a b c h
  have hleft := SquareZeroStrainRotation.rangeProjector_mul_commutator a b c h
  have hright := SquareZeroStrainRotation.commutator_mul_rangeProjector a b c h
  have hsq := SquareZeroStrainRotation.commutator_mul_self_eq_zero a b c h
  exact ⟨hfactor, hleft, hright, hsq⟩

/--
The Moore–Penrose anomaly is a square-zero element supported in the mixed
range/complement corner. This packages the two corner actions with its
nilpotency, which is the algebraic input needed by the fluid decomposition.
-/
theorem anomaly_mul_self_eq_zero
    (a b c : A) (h : IsMoorePenroseInverse a b) :
    (a * b) * EinsteinAnomaly a b c = EinsteinAnomaly a b c ∧
    EinsteinAnomaly a b c * (a * b) = 0 ∧
    EinsteinAnomaly a b c * EinsteinAnomaly a b c = 0 := by
  have hP : (a * b) * (a * b) = a * b := by
    exact SquareZeroStrainRotation.rangeProjector_mul_regularization a b b h
  have hrange : (a * b) * (a * c) = a * c := by
    exact SquareZeroStrainRotation.rangeProjector_mul_regularization a b c h
  have hfactor : EinsteinAnomaly a b c = (a * c) * (1 - a * b) := by
    exact SquareZeroStrainRotation.commutator_factorization a b c h
  have hleft : (a * b) * EinsteinAnomaly a b c = EinsteinAnomaly a b c := by
    rw [hfactor, ← mul_assoc, hrange]
  have hcomp : (1 - a * b) * (a * b) = 0 := by
    rw [sub_mul, one_mul, hP, sub_self]
  have hright : EinsteinAnomaly a b c * (a * b) = 0 := by
    rw [hfactor, mul_assoc, hcomp, mul_zero]
  have hkill : (1 - a * b) * (a * c) = 0 := by
    rw [sub_mul, one_mul, hrange, sub_self]
  have hsq : EinsteinAnomaly a b c * EinsteinAnomaly a b c = 0 := by
    rw [hfactor]
    calc
      ((a * c) * (1 - a * b)) * ((a * c) * (1 - a * b)) =
          (a * c) * ((1 - a * b) * (a * c)) * (1 - a * b) := by
            simp only [mul_assoc]
      _ = 0 := by rw [hkill]; simp
  exact ⟨hleft, hright, hsq⟩

/--
Self-adjoint regularization kills the anomaly and therefore all three pieces
of its mixed-corner profile.
-/
theorem anomaly_eq_zero_of_regularization_selfAdjoint
    (a b c : A) (h : IsMoorePenroseInverse a b)
    (hc : star (a * c) = a * c) :
    EinsteinAnomaly a b c = 0 ∧
    (a * b) * EinsteinAnomaly a b c = 0 ∧
    EinsteinAnomaly a b c * (a * b) = 0 := by
  have hz := SquareZeroStrainRotation.commutator_eq_zero_of_regularization_selfAdjoint a b c h hc
  have hz' : EinsteinAnomaly a b c = 0 := by
    simpa [EinsteinAnomaly] using hz
  refine ⟨hz', ?_, ?_⟩
  · rw [hz', mul_zero]
  · rw [hz', zero_mul]

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
  simpa only [strainRate, vorticity, ContinuousLinearMap.star_eq_adjoint] using
    SquareZeroStrainRotation.square_zero_scaled_star_pair (EinsteinAnomaly a b c)
      (anomaly_mul_self_eq_zero a b c h).2.2 ((2 : ℝ)⁻¹)

end Hilbert

end InfoGeometry.Canonical.AnomalyStrainRotation
