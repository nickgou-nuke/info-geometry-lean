import InfoGeometry.Topology.DiracKahlerMultiplication
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# The split Dirac–Kähler pair, retaining curvature

The identities in `RingIdentities` hold in every associative ring. They retain
the squares of both first-order operators, so no flatness is silently assigned
to a curved connection. The flat specialization consumes the existing
`DiracKahlerMultiplication.Data`, `dirac`, and `laplacian` owners.

This is an operator-algebra statement. Applying it to unbounded differential
operators requires a common invariant domain; it supplies no analytic domain,
spatial regularity, or Navier–Stokes reconstruction theorem.
-/

namespace InfoGeometry.Canonical.DiracKahlerSplitCurvature

section RingIdentities

variable {A : Type*} [Ring A]

/-- The positive square contains both curvature squares. -/
theorem plus_square_curvature (d δ : A) :
    (d + δ) * (d + δ) = (d * δ + δ * d) + (d * d + δ * δ) := by
  noncomm_ring

/-- The negative square reverses the mixed Laplacian and retains curvature. -/
theorem minus_square_curvature (d δ : A) :
    (d - δ) * (d - δ) = -(d * δ + δ * d) + (d * d + δ * δ) := by
  noncomm_ring

/-- The split anticommutator measures the difference of curvature squares. -/
theorem split_anticommutator_curvature (d δ : A) :
    (d + δ) * (d - δ) + (d - δ) * (d + δ) =
      (d * d - δ * δ) + (d * d - δ * δ) := by
  noncomm_ring

/-- The failure of `d` to commute with the mixed Laplacian retains `d²`. -/
theorem differential_laplacian_curvature (d δ : A) :
    d * (d * δ + δ * d) - (d * δ + δ * d) * d =
      (d * d) * δ - δ * (d * d) := by
  noncomm_ring

end RingIdentities

section FlatData

open InfoGeometry.Topology.DiracKahlerMultiplication

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The negative member of the existing real Dirac–Kähler doublet. -/
def negativeDirac (D : Data V) : V →ₗ[ℝ] V :=
  D.d - D.codifferential

/-- Flatness gives the negative Hodge square. -/
theorem negativeDirac_square (D : Data V) :
    (negativeDirac D).comp (negativeDirac D) = -(laplacian D) := by
  have hd : D.d * D.d = 0 := D.d_sq_zero
  have hδ : D.codifferential * D.codifferential = 0 :=
    D.codifferential_sq_zero
  change (D.d - D.codifferential) * (D.d - D.codifferential) =
    -(D.d * D.codifferential + D.codifferential * D.d)
  rw [minus_square_curvature, hd, hδ]
  simp

/-- The two first-order members anticommute on the existing flat datum. -/
theorem dirac_negativeDirac_anticommutator (D : Data V) :
    (dirac D).comp (negativeDirac D) +
      (negativeDirac D).comp (dirac D) = 0 := by
  have hd : D.d * D.d = 0 := D.d_sq_zero
  have hδ : D.codifferential * D.codifferential = 0 :=
    D.codifferential_sq_zero
  change (D.d + D.codifferential) * (D.d - D.codifferential) +
    (D.d - D.codifferential) * (D.d + D.codifferential) = 0
  rw [split_anticommutator_curvature, hd, hδ]
  simp

/-- The negative member remains odd for the existing form grading. -/
theorem negativeDirac_anticommutes_chirality (D : Data V) :
    (negativeDirac D).comp D.chirality =
      -(D.chirality.comp (negativeDirac D)) := by
  change (D.d - D.codifferential) * D.chirality =
    -(D.chirality * (D.d - D.codifferential))
  have hd : D.d * D.chirality = -(D.chirality * D.d) :=
    D.d_anticommutes
  have hδ : D.codifferential * D.chirality =
      -(D.chirality * D.codifferential) := D.codifferential_anticommutes
  rw [sub_mul, hd, hδ, mul_sub]
  abel

/-- Flat `d` commutes with the owner's Laplacian, as required by vorticity transport. -/
theorem differential_commutes_laplacian (D : Data V) :
    D.d.comp (laplacian D) = (laplacian D).comp D.d := by
  apply sub_eq_zero.mp
  change D.d * (D.d * D.codifferential + D.codifferential * D.d) -
    (D.d * D.codifferential + D.codifferential * D.d) * D.d = 0
  rw [differential_laplacian_curvature]
  have hd : D.d * D.d = 0 := D.d_sq_zero
  rw [hd]
  simp

end FlatData

end InfoGeometry.Canonical.DiracKahlerSplitCurvature
