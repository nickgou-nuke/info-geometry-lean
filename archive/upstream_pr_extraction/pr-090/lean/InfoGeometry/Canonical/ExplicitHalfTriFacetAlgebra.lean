import Mathlib.Tactic.Ring

/-!
# Explicit-Half Tri-Facet Projector Algebra

This file proves the algebraic decomposition associated to an element `P` with
`P^3 = P`, using an explicit scalar `half` satisfying `2 * half = 1`.  It avoids
typeclass-level inverse assumptions and proves the projector identities directly
from the supplied equation.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `P4_eq_P2`, `P_par_sum`, `P_par_idem`, `P_ext_idem`,
  `P_coext_idem`, `P_ortho_par_ext`, `P_ortho_par_coext`,
  `P_ortho_ext_coext`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  Every theorem is conditional on the explicit scalar law `2 * half = 1` and
  the cubic projector law `P^3 = P`.
- BUCKET 3: OPEN CLOSURE DEBT:
  None in this finite algebraic owner.
-/

namespace InfoGeometry.Canonical.ExplicitHalfTriFacetAlgebra

variable {R : Type*} [CommRing R]

/-- Cubic projector reduction: `P^3 = P` implies `P^4 = P^2`. -/
theorem P4_eq_P2 (P : R) (hP : P ^ 3 = P) :
    P ^ 4 = P ^ 2 := by
  have h1 : P ^ 4 = P * P ^ 3 := by ring
  rw [h1, hP]
  ring

/--
The parabolic, exact, and coexact pieces sum to unity with an explicit half
scalar.
-/
theorem P_par_sum (half P : R) (h_half : 2 * half = 1) :
    (1 - P ^ 2) + half * (P ^ 2 + P) + half * (P ^ 2 - P) = 1 := by
  calc
    (1 - P ^ 2) + half * (P ^ 2 + P) + half * (P ^ 2 - P)
        = 1 - P ^ 2 + (2 * half) * P ^ 2 := by ring
    _ = 1 - P ^ 2 + 1 * P ^ 2 := by rw [h_half]
    _ = 1 := by ring

/-- The parabolic component `1 - P^2` is idempotent. -/
theorem P_par_idem (P : R) (hP : P ^ 3 = P) :
    (1 - P ^ 2) ^ 2 = 1 - P ^ 2 := by
  have hP4 : P ^ 4 = P ^ 2 := P4_eq_P2 P hP
  calc
    (1 - P ^ 2) ^ 2 = 1 - 2 * P ^ 2 + P ^ 4 := by ring
    _ = 1 - 2 * P ^ 2 + P ^ 2 := by rw [hP4]
    _ = 1 - P ^ 2 := by ring

/-- The exact component `half * (P^2 + P)` is idempotent. -/
theorem P_ext_idem (half P : R) (h_half : 2 * half = 1) (hP : P ^ 3 = P) :
    (half * (P ^ 2 + P)) ^ 2 = half * (P ^ 2 + P) := by
  have hP4 : P ^ 4 = P ^ 2 := P4_eq_P2 P hP
  calc
    (half * (P ^ 2 + P)) ^ 2 = half ^ 2 * (P ^ 4 + 2 * P ^ 3 + P ^ 2) := by
      ring
    _ = half ^ 2 * (P ^ 2 + 2 * P + P ^ 2) := by rw [hP4, hP]
    _ = (half * (2 * half)) * (P ^ 2 + P) := by ring
    _ = (half * 1) * (P ^ 2 + P) := by rw [h_half]
    _ = half * (P ^ 2 + P) := by ring

/-- The coexact component `half * (P^2 - P)` is idempotent. -/
theorem P_coext_idem (half P : R) (h_half : 2 * half = 1) (hP : P ^ 3 = P) :
    (half * (P ^ 2 - P)) ^ 2 = half * (P ^ 2 - P) := by
  have hP4 : P ^ 4 = P ^ 2 := P4_eq_P2 P hP
  calc
    (half * (P ^ 2 - P)) ^ 2 = half ^ 2 * (P ^ 4 - 2 * P ^ 3 + P ^ 2) := by
      ring
    _ = half ^ 2 * (P ^ 2 - 2 * P + P ^ 2) := by rw [hP4, hP]
    _ = (half * (2 * half)) * (P ^ 2 - P) := by ring
    _ = (half * 1) * (P ^ 2 - P) := by rw [h_half]
    _ = half * (P ^ 2 - P) := by ring

/-- The parabolic and exact components are orthogonal. -/
theorem P_ortho_par_ext (half P : R) (hP : P ^ 3 = P) :
    (1 - P ^ 2) * (half * (P ^ 2 + P)) = 0 := by
  have hP4 : P ^ 4 = P ^ 2 := P4_eq_P2 P hP
  calc
    (1 - P ^ 2) * (half * (P ^ 2 + P)) =
        half * (P ^ 2 + P - P ^ 4 - P ^ 3) := by ring
    _ = half * (P ^ 2 + P - P ^ 2 - P) := by rw [hP4, hP]
    _ = 0 := by ring

/-- The parabolic and coexact components are orthogonal. -/
theorem P_ortho_par_coext (half P : R) (hP : P ^ 3 = P) :
    (1 - P ^ 2) * (half * (P ^ 2 - P)) = 0 := by
  have hP4 : P ^ 4 = P ^ 2 := P4_eq_P2 P hP
  calc
    (1 - P ^ 2) * (half * (P ^ 2 - P)) =
        half * (P ^ 2 - P - P ^ 4 + P ^ 3) := by ring
    _ = half * (P ^ 2 - P - P ^ 2 + P) := by rw [hP4, hP]
    _ = 0 := by ring

/-- The exact and coexact components are orthogonal. -/
theorem P_ortho_ext_coext (half P : R) (hP : P ^ 3 = P) :
    (half * (P ^ 2 + P)) * (half * (P ^ 2 - P)) = 0 := by
  have hP4 : P ^ 4 = P ^ 2 := P4_eq_P2 P hP
  calc
    (half * (P ^ 2 + P)) * (half * (P ^ 2 - P)) = half ^ 2 * (P ^ 4 - P ^ 2) := by
      ring
    _ = half ^ 2 * (P ^ 2 - P ^ 2) := by rw [hP4]
    _ = 0 := by ring

end InfoGeometry.Canonical.ExplicitHalfTriFacetAlgebra
