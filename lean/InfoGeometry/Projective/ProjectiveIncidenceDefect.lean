/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.HessianThermodynamicManifold

/-!
# Projective incidence defects and three-point holonomy

On a scalar affine chart, the primal--dual incidence pairing is `η * θ`.
The defect is the Fenchel slack
`ψ θ + ψ⋆ η - η θ`.  The identities below are algebraic: they do not turn an
affine chart into a projective quotient, and contact/orthogonality hypotheses
are kept explicit when passing from the cocycle identity to additivity.
-/

namespace InfoGeometry.Projective.ProjectiveIncidenceDefect

open InfoGeometry.Algebra.HessianThermodynamicManifold

/-- Fenchel/ incidence defect at a primal coordinate and a dual coordinate. -/
def projectiveIncidenceDefect
    (ψ ψStar : ℝ → ℝ) (θ η : ℝ) : ℝ :=
  ψ θ + ψStar η - η * θ

/-- Legendre contact makes the incidence defect vanish. -/
theorem projectiveIncidenceDefect_eq_zero_of_legendre_contact
    (ψ ψStar grad : ℝ → ℝ)
    (pair : FenchelDualPair ψ ψStar grad) (θ : ℝ) :
    projectiveIncidenceDefect ψ ψStar θ (grad θ) = 0 := by
  unfold projectiveIncidenceDefect
  have h := pair.legendre_identity θ
  simpa [InnerSpace.inner] using sub_eq_zero.mpr h

/-- Three-point cocycle identity for incidence defects. -/
theorem projectiveIncidenceDefect_three_point_cocycle
    (ψ ψStar : ℝ → ℝ) (θ₁ θ₂ : ℝ) (η₂ η₃ : ℝ) :
    projectiveIncidenceDefect ψ ψStar θ₁ η₃ =
      projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ -
          projectiveIncidenceDefect ψ ψStar θ₂ η₂ +
            (η₂ - η₃) * (θ₁ - θ₂) := by
  unfold projectiveIncidenceDefect
  ring

/-- Additivity follows from contact at the intermediate point and orthogonality
of the intermediate primal/dual displacement. -/
theorem projectiveIncidenceDefect_additive_of_orthogonal
    (ψ ψStar : ℝ → ℝ) (θ₁ θ₂ : ℝ) (η₂ η₃ : ℝ)
    (hcontact : projectiveIncidenceDefect ψ ψStar θ₂ η₂ = 0)
    (horth : (η₂ - η₃) * (θ₁ - θ₂) = 0) :
    projectiveIncidenceDefect ψ ψStar θ₁ η₃ =
      projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ := by
  rw [projectiveIncidenceDefect_three_point_cocycle]
  rw [hcontact, horth]
  ring

/-- Triangle holonomy: all potential values cancel, leaving only the
bilinear point--hyperplane pairings. -/
theorem projectiveIncidenceDefect_triangle_holonomy
    (ψ ψStar : ℝ → ℝ)
    (θ₁ θ₂ θ₃ η₁ η₂ η₃ : ℝ) :
    projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ +
        projectiveIncidenceDefect ψ ψStar θ₃ η₁ -
      (projectiveIncidenceDefect ψ ψStar θ₁ η₁ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₃ η₃) =
      η₁ * (θ₁ - θ₃) + η₂ * (θ₂ - θ₁) + η₃ * (θ₃ - θ₂) := by
  unfold projectiveIncidenceDefect
  ring

end InfoGeometry.Projective.ProjectiveIncidenceDefect
