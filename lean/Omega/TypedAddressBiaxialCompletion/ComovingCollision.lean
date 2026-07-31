import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete input data for the equal-depth comoving collision regime. The Vandermonde lower bound
is recorded as a real inequality, and the near-collision blowup is phrased as the equal-depth
specialization of that lower bound. -/
structure ComovingCollisionData where
  depth : ℕ
  separation : ℝ
  amplification : ℝ
  vandermondeLower : ℝ

/-- Paper-facing wrapper for the typed-address biaxial completion comoving-collision estimate.
    cor:typed-address-biaxial-completion-comoving-collision -/
theorem paper_typed_address_biaxial_completion_comoving_collision
    (D : ComovingCollisionData)
    (amplification_lower : D.vandermondeLower ≤ D.amplification)
    (near_collision_blowup :
      D.separation ≤ 1 / ((D.depth : ℝ) + 1) → ((D.depth : ℝ) + 1) ≤ D.amplification) :
    D.vandermondeLower ≤ D.amplification ∧
      (D.separation ≤ 1 / ((D.depth : ℝ) + 1) → ((D.depth : ℝ) + 1) ≤ D.amplification) := by
  exact ⟨amplification_lower, near_collision_blowup⟩

end Omega.TypedAddressBiaxialCompletion
