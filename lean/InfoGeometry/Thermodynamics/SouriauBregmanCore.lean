import InfoGeometry.Convex.Bregman

/-!
# The theorem-safe Souriau/Bregman core

This owner contains only the tangent-subtraction algebra.  Analytic
properties of a particular Massieu potential (zeta, xi, or otherwise) are
downstream hypotheses.  In particular, nonnegativity is exposed through the
supporting-tangent inequality rather than being inferred from symmetry.
-/

namespace InfoGeometry.SouriauBregmanCore

/-- Souriau's one-dimensional tangent subtraction, using the canonical
`InfoGeometry.bregmanDiv` definition. -/
noncomputable def divergence (Φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  InfoGeometry.bregmanDiv Φ x y

@[simp]
theorem divergence_self (Φ : ℝ → ℝ) (x : ℝ) :
    divergence Φ x x = 0 := by
  exact InfoGeometry.bregmanDiv_self Φ x

/-- Expanded form of the tangent subtraction. -/
theorem divergence_eq_tangent_subtraction
    (Φ : ℝ → ℝ) (x y : ℝ) :
    divergence Φ x y =
      Φ x - (Φ y + deriv Φ y * (x - y)) := by
  simp [divergence, InfoGeometry.bregmanDiv]
  ring

/-- The familiar Massieu form when the dual readout is `Q = -Φ'`. -/
theorem divergence_eq_dual_readout
    (Φ Q : ℝ → ℝ)
    (hQ : ∀ y, Q y = -deriv Φ y)
    (x y : ℝ) :
    divergence Φ x y =
      Φ x - Φ y + Q y * (x - y) := by
  rw [divergence_eq_tangent_subtraction, hQ]
  ring

/-- Bregman nonnegativity from an explicit supporting-tangent inequality.

This is the exact downstream contract supplied by convexity/regularity
owners.  No positivity or convexity is silently inferred here. -/
theorem divergence_nonneg_of_supporting_tangent
    (Φ : ℝ → ℝ)
    (hΦ : ∀ x y : ℝ,
      Φ y + deriv Φ y * (x - y) ≤ Φ x)
    (x y : ℝ) :
    0 ≤ divergence Φ x y := by
  rw [divergence_eq_tangent_subtraction]
  linarith [hΦ x y]

end InfoGeometry.SouriauBregmanCore
