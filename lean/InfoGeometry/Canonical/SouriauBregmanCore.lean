import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Souriau--Bregman scalar core

This file owns the finite real algebra of a Bregman gap.  It deliberately
does not choose a logarithm branch, a zeta function, or a differentiability
domain.  Positivity is obtained only from an explicit first-order convexity
inequality.
-/

namespace InfoGeometry.Canonical.SouriauBregmanCore

/-! ## The gap and its algebraic identities -/

/-- The scalar Bregman gap attached to a potential and a first-order readout. -/
def bregmanGap (Φ dΦ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Φ x - Φ y - dΦ y * (x - y)

@[simp]
theorem bregmanGap_self (Φ dΦ : ℝ → ℝ) (x : ℝ) :
    bregmanGap Φ dΦ x x = 0 := by
  simp [bregmanGap]

theorem bregmanGap_threePoint
    (Φ dΦ : ℝ → ℝ) (x y z : ℝ) :
    bregmanGap Φ dΦ x z =
      bregmanGap Φ dΦ x y + bregmanGap Φ dΦ y z
        + (dΦ y - dΦ z) * (x - y) := by
  unfold bregmanGap
  ring

theorem bregmanGap_symm_sum
    (Φ dΦ : ℝ → ℝ) (x y : ℝ) :
    bregmanGap Φ dΦ x y + bregmanGap Φ dΦ y x =
      (dΦ x - dΦ y) * (x - y) := by
  unfold bregmanGap
  ring

/-- Adding an affine function to a potential does not change its Bregman gap. -/
theorem bregmanGap_affine_gauge_invariant
    (Φ dΦ : ℝ → ℝ) (a b x y : ℝ) :
    bregmanGap (fun t => Φ t + a * t + b) (fun t => dΦ t + a) x y =
      bregmanGap Φ dΦ x y := by
  unfold bregmanGap
  ring

theorem bregmanGap_of_stationary
    (Φ dΦ : ℝ → ℝ) {y : ℝ} (hy : dΦ y = 0) (x : ℝ) :
    bregmanGap Φ dΦ x y = Φ x - Φ y := by
  simp [bregmanGap, hy]

/-! ## Honest convexity boundary -/

/--
The exact first-order hypothesis needed by the scalar Bregman nonnegativity
theorem.  This is intentionally weaker than choosing a global differentiable
or analytic potential.
-/
structure FirstOrderConvexityDatum (Φ dΦ : ℝ → ℝ) : Prop where
  lower_bound : ∀ x y, Φ y + dΦ y * (x - y) ≤ Φ x

theorem bregmanGap_nonneg
    (Φ dΦ : ℝ → ℝ)
    (C : FirstOrderConvexityDatum Φ dΦ)
    (x y : ℝ) :
    0 ≤ bregmanGap Φ dΦ x y := by
  unfold bregmanGap
  linarith [C.lower_bound x y]

theorem bregmanGap_eq_zero_of_stationary_and_equal
    (Φ dΦ : ℝ → ℝ) {y : ℝ} (hy : dΦ y = 0)
    (hxy : Φ x = Φ y) :
    bregmanGap Φ dΦ x y = 0 := by
  rw [bregmanGap_of_stationary Φ dΦ hy x, hxy]
  exact sub_self _

end InfoGeometry.Canonical.SouriauBregmanCore
