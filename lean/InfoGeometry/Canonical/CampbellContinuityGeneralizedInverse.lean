import Mathlib

/-!
# Campbell Continuity of Generalized Inverses

Finite algebraic layer extracted from Stephen L. Campbell, "On Continuity of
the Moore-Penrose and Drazin Generalized Inverses" (Linear Algebra and its
Applications 18, 1977, 53--57).

The paper derives norm estimates from exact block decompositions of the
perturbation `F = X - A⁺` or `F = X - A#`.  This file formalizes the
theorem-safe algebraic decompositions.  The analytic norm estimates are checked
on exact rational examples by external scripts.

#### BUCKET 1: CLOSED FINITE THEOREMS
Pure ring decompositions by complementary projectors and their Moore-Penrose
and group-inverse residual substitutions.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The residual substitutions are explicit named premises.  No hidden
generalized-inverse existence theorem is assumed.

#### BUCKET 3: OPEN CLOSURE DEBT
The full complex matrix norm continuity theorem, uniqueness of Moore-Penrose
and Drazin inverses, and convergence of arbitrary matrix sequences are not
asserted in Lean here.
-/

namespace InfoGeometry.Canonical.CampbellContinuityGeneralizedInverse

variable {R : Type} [Ring R]

/-- Splitting any element by two complementary idempotent-shaped cuts. -/
theorem twoProjector_decomposition (P Q F : R) :
    F = P * F * Q + (1 - P) * F * Q + P * F * (1 - Q) + (1 - P) * F * (1 - Q) := by
  noncomm_ring

/-- Splitting any element by one complementary cut on both sides. -/
theorem oneProjector_decomposition (P F : R) :
    F = P * F * P + P * F * (1 - P) + (1 - P) * F * P + (1 - P) * F * (1 - P) := by
  noncomm_ring

/--
Campbell's Moore-Penrose perturbation identity after the four residual blocks
have been solved.
-/
theorem moorePenrose_residual_decomposition
    (A Ap F E₁ E₂ E₃ E₄ : R)
    (h₁₁ : (Ap * A) * F * (A * Ap) = Ap * E₁ * Ap)
    (h₁₀ : (Ap * A) * F * (1 - A * Ap) = Ap * E₃ * (1 - A * Ap))
    (h₀₁ : (1 - Ap * A) * F * (A * Ap) = (1 - Ap * A) * E₄ * Ap)
    (h₀₀ :
      (1 - Ap * A) * F * (1 - A * Ap)
        = (1 - Ap * A) * (-E₂ + E₄ * Ap * E₃) * (1 - A * Ap)) :
    F =
      Ap * E₁ * Ap
        + (1 - Ap * A) * E₄ * Ap
        + Ap * E₃ * (1 - A * Ap)
        + (1 - Ap * A) * (-E₂ + E₄ * Ap * E₃) * (1 - A * Ap) := by
  calc
    F =
        (Ap * A) * F * (A * Ap)
          + (1 - Ap * A) * F * (A * Ap)
          + (Ap * A) * F * (1 - A * Ap)
          + (1 - Ap * A) * F * (1 - A * Ap) := by
      exact twoProjector_decomposition (Ap * A) (A * Ap) F
    _ =
        Ap * E₁ * Ap
          + (1 - Ap * A) * E₄ * Ap
          + Ap * E₃ * (1 - A * Ap)
          + (1 - Ap * A) * (-E₂ + E₄ * Ap * E₃) * (1 - A * Ap) := by
      rw [h₁₁, h₀₁, h₁₀, h₀₀]

/--
Campbell's index-one Drazin/group-inverse perturbation identity after the
residual blocks have been solved.
-/
theorem groupInverse_residual_decomposition
    (A Ag F E₁ E₂ E₃ : R)
    (h₁₁ : (Ag * A) * F * (Ag * A) = Ag * Ag * E₃ * (Ag * A))
    (h₁₀ : (Ag * A) * F * (1 - Ag * A) = -Ag * E₂ * (1 - Ag * A))
    (h₀₁ : (1 - Ag * A) * F * (Ag * A) = (1 - Ag * A) * E₂ * Ag)
    (h₀₀ :
      (1 - Ag * A) * F * (1 - Ag * A)
        = (1 - Ag * A) * (-E₂ * Ag * E₂ - E₁) * (1 - Ag * A)) :
    F =
      Ag * Ag * E₃ * (Ag * A)
        + -Ag * E₂ * (1 - Ag * A)
        + (1 - Ag * A) * E₂ * Ag
        + (1 - Ag * A) * (-E₂ * Ag * E₂ - E₁) * (1 - Ag * A) := by
  calc
    F =
        (Ag * A) * F * (Ag * A)
          + (Ag * A) * F * (1 - Ag * A)
          + (1 - Ag * A) * F * (Ag * A)
          + (1 - Ag * A) * F * (1 - Ag * A) := by
      exact oneProjector_decomposition (Ag * A) F
    _ =
        Ag * Ag * E₃ * (Ag * A)
          + -Ag * E₂ * (1 - Ag * A)
          + (1 - Ag * A) * E₂ * Ag
          + (1 - Ag * A) * (-E₂ * Ag * E₂ - E₁) * (1 - Ag * A) := by
      rw [h₁₁, h₁₀, h₀₁, h₀₀]

end InfoGeometry.Canonical.CampbellContinuityGeneralizedInverse
