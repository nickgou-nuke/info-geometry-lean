import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Hodge-Krein Tri-Facet Projector Algebra

This file proves the finite algebraic projector calculus attached to a linear
operator `O` satisfying the cubic relation `O^3 = O`.  In the Hodge-Krein
dictionary, the three projectors are the exact, coexact, and harmonic shadows
of the formal roots `+1`, `-1`, and `0`.

This is a linear-algebraic theorem owner only.  It does not assert that `O` is
a geometric Hodge Laplacian on a manifold, nor does it construct analytic
Hodge representatives.

The operator theorems below are finite linear-algebra statements conditional on
the explicit cubic law `∀ x, O (O (O x)) = O x`.  Geometric Hodge theory, Krein
signatures, and Drazin inverses are separate owner files and are not asserted by
this projector calculus.
-/

namespace InfoGeometry.Canonical.HodgeKreinTriFacetProjectors

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Scalar half of a doubled vector is the vector. -/
theorem half_smul_add_self (x : V) :
    ((1 / 2 : ℝ) • (x + x)) = x := by
  module

/-- Scalar half of `x - (-x)` is `x`. -/
theorem half_smul_sub_neg_self (x : V) :
    ((1 / 2 : ℝ) • (x - -x)) = x := by
  module

/-- The two half-scaled `a ± b` components recover `a`. -/
theorem half_smul_add_sub_eq_left (a b : V) :
    (1 / 2 : ℝ) • (a + b) + (1 / 2 : ℝ) • (a - b) = a := by
  module

/-- Exact-sector projector: `P_ext = 1/2 * (O^2 + O)`. -/
noncomputable def P_ext (O : V →ₗ[ℝ] V) (x : V) : V :=
  (1 / 2 : ℝ) • (O (O x) + O x)

/-- Coexact-sector projector: `P_coext = 1/2 * (O^2 - O)`. -/
noncomputable def P_coext (O : V →ₗ[ℝ] V) (x : V) : V :=
  (1 / 2 : ℝ) • (O (O x) - O x)

/-- Harmonic-sector projector: `P_harm = I - O^2`. -/
noncomputable def P_harm (O : V →ₗ[ℝ] V) (x : V) : V :=
  x - O (O x)

/-- Drazin/Hodge compact-core projector: `P_core = O^2`. -/
noncomputable def P_core (O : V →ₗ[ℝ] V) (x : V) : V :=
  O (O x)

/-- Drazin/Hodge nilpotent-boundary projector: `P_nil = I - O^2`. -/
noncomputable def P_nil (O : V →ₗ[ℝ] V) (x : V) : V :=
  x - O (O x)

/-- The exact projector lands in the `+1` eigensector. -/
theorem O_P_ext
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    O (P_ext O x) = P_ext O x := by
  unfold P_ext
  rw [map_smul, map_add, hO x, add_comm]

/-- The exact projector is also fixed by `O^2`. -/
theorem O_O_P_ext
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    O (O (P_ext O x)) = P_ext O x := by
  rw [O_P_ext O hO x]
  rw [O_P_ext O hO x]

/-- The coexact projector lands in the `-1` eigensector. -/
theorem O_P_coext
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    O (P_coext O x) = -P_coext O x := by
  unfold P_coext
  rw [map_smul, map_sub, hO x]
  module

/-- The coexact projector is fixed by `O^2`. -/
theorem O_O_P_coext
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    O (O (P_coext O x)) = P_coext O x := by
  rw [O_P_coext O hO x]
  rw [map_neg, O_P_coext O hO x]
  abel

/-- The harmonic projector lands in the kernel of `O`. -/
theorem O_P_harm
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    O (P_harm O x) = 0 := by
  unfold P_harm
  rw [map_sub, hO x]
  abel

/-- The harmonic projector also lands in the kernel of `O^2`. -/
theorem O_O_P_harm
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    O (O (P_harm O x)) = 0 := by
  rw [O_P_harm O hO x, map_zero]

/-- Exact and coexact pieces sum to the compact core `O^2`. -/
theorem P_ext_add_P_coext_eq_P_core (O : V →ₗ[ℝ] V) (x : V) :
    P_ext O x + P_coext O x = P_core O x := by
  unfold P_ext P_coext P_core
  exact half_smul_add_sub_eq_left (O (O x)) (O x)

/-- The exact, coexact, and harmonic projectors partition the vector. -/
theorem P_ext_add_P_coext_add_P_harm (O : V →ₗ[ℝ] V) (x : V) :
    P_ext O x + P_coext O x + P_harm O x = x := by
  rw [P_ext_add_P_coext_eq_P_core]
  unfold P_core P_harm
  abel

/-- The exact-sector projector is idempotent. -/
theorem P_ext_idem
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_ext O (P_ext O x) = P_ext O x := by
  change (1 / 2 : ℝ) • (O (O (P_ext O x)) + O (P_ext O x)) = P_ext O x
  rw [O_O_P_ext O hO x, O_P_ext O hO x]
  exact half_smul_add_self (P_ext O x)

/-- The coexact-sector projector is idempotent. -/
theorem P_coext_idem
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_coext O (P_coext O x) = P_coext O x := by
  change (1 / 2 : ℝ) • (O (O (P_coext O x)) - O (P_coext O x)) = P_coext O x
  rw [O_O_P_coext O hO x, O_P_coext O hO x]
  exact half_smul_sub_neg_self (P_coext O x)

/-- The harmonic-sector projector is idempotent. -/
theorem P_harm_idem
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_harm O (P_harm O x) = P_harm O x := by
  change P_harm O x - O (O (P_harm O x)) = P_harm O x
  rw [O_O_P_harm O hO x]
  abel

/-- The exact projection annihilates the coexact sector. -/
theorem P_ext_P_coext
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_ext O (P_coext O x) = 0 := by
  unfold P_ext
  rw [O_O_P_coext O hO x, O_P_coext O hO x]
  module

/-- The coexact projection annihilates the exact sector. -/
theorem P_coext_P_ext
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_coext O (P_ext O x) = 0 := by
  unfold P_coext
  rw [O_O_P_ext O hO x, O_P_ext O hO x]
  module

/-- The exact projection annihilates the harmonic sector. -/
theorem P_ext_P_harm
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_ext O (P_harm O x) = 0 := by
  unfold P_ext
  rw [O_O_P_harm O hO x, O_P_harm O hO x]
  simp

/-- The harmonic projection annihilates the exact sector. -/
theorem P_harm_P_ext
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_harm O (P_ext O x) = 0 := by
  unfold P_harm
  rw [O_O_P_ext O hO x]
  abel

/-- The coexact projection annihilates the harmonic sector. -/
theorem P_coext_P_harm
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_coext O (P_harm O x) = 0 := by
  unfold P_coext
  rw [O_O_P_harm O hO x, O_P_harm O hO x]
  simp

/-- The harmonic projection annihilates the coexact sector. -/
theorem P_harm_P_coext
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_harm O (P_coext O x) = 0 := by
  unfold P_harm
  rw [O_O_P_coext O hO x]
  abel

/-- The compact core is the exact plus coexact sector. -/
theorem P_core_eq_P_ext_add_P_coext (O : V →ₗ[ℝ] V) (x : V) :
    P_core O x = P_ext O x + P_coext O x := by
  exact (P_ext_add_P_coext_eq_P_core O x).symm

/-- The compact core and nilpotent boundary partition the vector. -/
theorem P_core_add_P_nil (O : V →ₗ[ℝ] V) (x : V) :
    P_core O x + P_nil O x = x := by
  unfold P_core P_nil
  abel

/-- The core projection annihilates the nilpotent boundary. -/
theorem P_core_P_nil
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_core O (P_nil O x) = 0 := by
  unfold P_core P_nil
  rw [map_sub, hO x]
  rw [sub_self, map_zero]

/-- The nilpotent boundary annihilates the core projection. -/
theorem P_nil_P_core
    (O : V →ₗ[ℝ] V)
    (hO : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_nil O (P_core O x) = 0 := by
  unfold P_nil P_core
  rw [hO (O x)]
  abel

end InfoGeometry.Canonical.HodgeKreinTriFacetProjectors
