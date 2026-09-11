import InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.WittProjectiveClosure
import Mathlib.Tactic

/-!
# Bipolar projective connection and the repository Witt/Virasoro owner

The polynomial vector fields `1`, `s`, and `s²` correspond, up to the chosen
sign convention for basis generators, to the Witt modes indexed by
`{-1,0,1}`.  The repository already owns this projective-mode carrier and proves
that the Virasoro cocycle vanishes there.

This file therefore does not introduce a second Witt or Virasoro algebra.  It
joins two independent statements:

* the analytic coefficient `P_c(s)=-(c/12) S_W(s)` has the algebraic Ward
  transformation law and quadratic vector fields have zero third derivative;
* the genuine repository Witt/Virasoro cocycle vanishes on the three
  projective modes and their nonzero brackets remain in that mode set.

No Hilbert-space representation, vacuum vector, positive-energy theorem, or
identification of the scalar parameter `c` with the central element of a
specific representation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarWittProjectiveWardBridge

open VirasoroProject
open VirasoroProject.WittAlgebra
open InfoGeometry.Algebra.WittProjectiveClosureHonest
open InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection

/-- The anomaly polynomial vanishes on every repository-owned projective mode. -/
theorem projective_mode_anomalyFactor_zero
    {m : ℤ} (hm : m ∈ ProjectiveClosure) :
    anomalyFactor m = 0 := by
  exact anomalyFactor_eq_zero_of_mem_projective hm

/-- The genuine Virasoro two-cocycle vanishes when the left Witt mode is one of
`{-1,0,1}`. -/
theorem projective_mode_virasoroCocycle_left_zero
    (m n : ℤ) (hm : m ∈ ProjectiveClosure) :
    virasoroCocycle ℂ (lgen ℂ m) (lgen ℂ n) = 0 := by
  exact virasoroCocycle_lgen_left_projective_zero ℂ m n hm

/-- Symmetric right-slot form of projective cocycle vanishing. -/
theorem projective_mode_virasoroCocycle_right_zero
    (m n : ℤ) (hn : n ∈ ProjectiveClosure) :
    virasoroCocycle ℂ (lgen ℂ m) (lgen ℂ n) = 0 := by
  exact virasoroCocycle_lgen_right_projective_zero ℂ m n hn

/-- On projective modes the bracket is the centerless Witt bracket. -/
theorem projective_mode_bracket
    (m n : ℤ) (hm : m ∈ ProjectiveClosure)
    (hn : n ∈ ProjectiveClosure) :
    ⁅lgen ℂ m, lgen ℂ n⁆ =
      (m - n : ℂ) • lgen ℂ (m + n) := by
  exact projective_bracket_eq_witt ℂ m n hm hn

/-- A nonzero bracket of two projective modes remains in the projective mode
set. -/
theorem projective_mode_nonzero_bracket_closed
    {m n : ℤ} (hm : m ∈ ProjectiveClosure)
    (hn : n ∈ ProjectiveClosure) (hcoeff : (m - n : ℂ) ≠ 0) :
    m + n ∈ ProjectiveClosure := by
  exact projective_sum_mem_of_bracket_coeff_ne_zero ℂ hm hn hcoeff

/-- Exact separation of the two anomaly statements: local third derivatives
vanish for quadratic polynomial vector fields, and the native Virasoro cocycle
vanishes on the corresponding projective mode set. -/
theorem bipolar_projective_anomaly_packet
    (c : ℂ) (v : ProjectiveVectorField) (s : ℂ)
    (m n : ℤ) (hm : m ∈ ProjectiveClosure)
    (hn : n ∈ ProjectiveClosure) :
    (c / 12) * v.third s = 0 ∧
      anomalyFactor m = 0 ∧
      virasoroCocycle ℂ (lgen ℂ m) (lgen ℂ n) = 0 ∧
      ⁅lgen ℂ m, lgen ℂ n⁆ =
        (m - n : ℂ) • lgen ℂ (m + n) := by
  exact ⟨by simp [ProjectiveVectorField.third],
    projective_mode_anomalyFactor_zero hm,
    projective_mode_virasoroCocycle_left_zero m n hm,
    projective_mode_bracket m n hm hn⟩

end InfoGeometry.Canonical.BipolarWittProjectiveWardBridge
