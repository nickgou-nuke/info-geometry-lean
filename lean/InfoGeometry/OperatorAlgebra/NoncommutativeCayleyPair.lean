/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

/-!
# Two-sided Cayley resolvents in a noncommutative ring

The algebraic Cayley identities are stated for an arbitrary associative ring
and explicit left and right inverses of `1 + x` and `1 - x`. They require no
matrix coordinates and assert no analytic or topological compactification.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeCayleyPair

variable {A : Type*} [Ring A]

/-- The forward right-resolvent Cayley transform. -/
def cayley (x rPlus : A) : A := (1 - x) * rPlus

/-- The sign-reflected Cayley transform, using the other resolvent. -/
def cayleyReflected (x rMinus : A) : A := (1 + x) * rMinus

/-- The polynomial factors commute in any associative ring. -/
theorem cayley_factors_commute (x : A) :
    (1 - x) * (1 + x) = (1 + x) * (1 - x) := by
  noncomm_ring

/-- The two sign-related Cayley transforms are exact two-sided inverses. -/
theorem cayley_reflection_is_inverse {x rPlus rMinus : A}
    (hPlus : (1 + x) * rPlus = 1)
    (hPlusRev : rPlus * (1 + x) = 1)
    (hMinus : (1 - x) * rMinus = 1)
    (hMinusRev : rMinus * (1 - x) = 1) :
    cayley x rPlus * cayleyReflected x rMinus = 1 ∧
      cayleyReflected x rMinus * cayley x rPlus = 1 := by
  constructor
  · unfold cayley cayleyReflected
    calc
      (1 - x) * rPlus * ((1 + x) * rMinus) =
          (1 - x) * (rPlus * (1 + x)) * rMinus := by noncomm_ring
      _ = (1 - x) * 1 * rMinus := by rw [hPlusRev]
      _ = 1 := by rw [mul_one, hMinus]
  · unfold cayleyReflected cayley
    calc
      (1 + x) * rMinus * ((1 - x) * rPlus) =
          (1 + x) * (rMinus * (1 - x)) * rPlus := by noncomm_ring
      _ = (1 + x) * 1 * rPlus := by rw [hMinusRev]
      _ = 1 := by rw [mul_one, hPlus]

/-- Pole sum and difference identities for the operator Cayley transform. -/
theorem cayley_pole_identities {x rPlus : A}
    (hPlus : (1 + x) * rPlus = 1) :
    1 + cayley x rPlus = 2 • rPlus ∧
      1 - cayley x rPlus = 2 • (x * rPlus) := by
  unfold cayley
  constructor
  · calc
      1 + (1 - x) * rPlus = (1 + x) * rPlus + (1 - x) * rPlus := by
        rw [hPlus]
      _ = ((1 + x) + (1 - x)) * rPlus := by rw [← add_mul]
      _ = 2 • rPlus := by simp; noncomm_ring
  · calc
      1 - (1 - x) * rPlus = (1 + x) * rPlus - (1 - x) * rPlus := by
        rw [hPlus]
      _ = ((1 + x) - (1 - x)) * rPlus := by rw [← sub_mul]
      _ = 2 • (x * rPlus) := by simp; noncomm_ring

end InfoGeometry.OperatorAlgebra.NoncommutativeCayleyPair

namespace InfoGeometry.OperatorAlgebra.NoncommutativeCayleyPair

section IdempotentResolvent

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The operator-valued shifted quadratic factorization used by the Peirce
mass decomposition. The parameter `μ` acts centrally through the algebra
structure; `E` and `M` remain arbitrary noncommuting operators, related only
by the exact quadratic identity `E * E = M`. This is an algebraic identity,
not a spectral-gap assertion. -/
theorem shifted_operator_factorization {μ : R} {E M : A}
    (hE : E * E = M) :
    (algebraMap R A μ - E) * (algebraMap R A μ + E) =
      algebraMap R A (μ ^ 2) * (1 - M) +
        algebraMap R A (μ ^ 2 - 1) * M := by
  have hcentral : algebraMap R A μ * E = E * algebraMap R A μ :=
    Algebra.commutes μ E
  calc
    _ = algebraMap R A (μ ^ 2) - M := by
      rw [map_pow]
      noncomm_ring [hE, hcentral]
    _ = algebraMap R A (μ ^ 2) * (1 - M) +
        algebraMap R A (μ ^ 2 - 1) * M := by
      rw [map_sub, map_one, map_pow]
      noncomm_ring

end IdempotentResolvent

end InfoGeometry.OperatorAlgebra.NoncommutativeCayleyPair
