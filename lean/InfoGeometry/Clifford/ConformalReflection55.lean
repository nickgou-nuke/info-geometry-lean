import InfoGeometry.Clifford.ConformalLift55
import Mathlib.Tactic.NoncommRing

/-!
# Conformal Reflection Generator and Sandwich Swap in Cl(5,5)

This file defines the conformal reflection generator `J = n₀ − n∞` from
a `ConformalNullPair` in `Cl(5,5)` and proves the sandwich-swap identities:

* `J² = −1`  (the conformal reflection squares to minus the identity)
* `J · n₀ · J = n∞`  (the reflection maps the origin to infinity)
* `J · n∞ · J = n₀`  (the reflection maps infinity to the origin)
* `J · (−J) = 1` and `(−J) · J = 1`  (J is a unit with inverse −J)

These identities formalize the core algebraic mechanism of Möbius inversion:
the reflection generator swaps the origin and the point at infinity in
conformal geometric algebra, realizing the compactification of the Poincaré ball.

## Mathematical context

The `ConformalNullPair` structure (from `ConformalLift55`) records a null pair
`(u, v)` in the extra `Cl(1,1)` factor of `Cl(5,5) ≃ Cl(4,4) ⊗̂ Cl(1,1)`
satisfying `u² = 0`, `v² = 0`, `uv + vu = 1`.

In CGA conventions:
- `u` plays the role of the origin representative `n₀`
- `v` plays the role of the infinity representative `n∞`
- `J = u − v` is the conformal inversion operator

The key sandwich identities `JuJ = v` and `JvJ = u` are proved by expanding
the products and using the null-pair axioms to cancel terms, leaving exactly
the swapped element.

## Closure status

These are **native Lean proofs** — no axioms, sorry, or external certificates.
Each theorem is a kernel-checked derivation from the `ConformalNullPair` axioms
(`u² = 0`, `v² = 0`, `uv + vu = 1`).
-/

noncomputable section

namespace InfoGeometry.Clifford.ConformalReflection55

open InfoGeometry.Clifford.ConformalLift55

/-- The conformal reflection generator `J = n₀ − n∞`.

In CGA, this operator implements Möbius inversion via the sandwich product
`x ↦ J x J`. It swaps the algebraic representations of the origin and
the point at infinity. -/
def J (p : ConformalNullPair) : Cl55 := p.u - p.v

variable (p : ConformalNullPair)

/-! ### Core identity: J² = −1 -/

/--
`J² = −1`: the conformal reflection generator squares to minus the identity.

This is the algebraic signature of a conformal inversion: the operator
is not a simple reflection (`J² = 1`) but a Clifford unit with `J² = −1`,
encoding the non-trivial topology of the conformally compactified space.
-/
theorem J_sq : J p ^ 2 = -1 := by
  unfold J
  have hu : p.u * p.u = 0 := by rw [← sq]; exact p.u_square
  have hv : p.v * p.v = 0 := by rw [← sq]; exact p.v_square
  calc (p.u - p.v) ^ 2
      = p.u * p.u - p.u * p.v - p.v * p.u + p.v * p.v := by noncomm_ring
    _ = 0 - p.u * p.v - p.v * p.u + 0 := by rw [hu, hv]
    _ = -(p.u * p.v + p.v * p.u) := by noncomm_ring
    _ = -1 := by rw [p.anticomm]

/-! ### Sandwich swap: origin ↔ infinity -/

/--
Sandwich swap (origin → infinity): `J · n₀ · J = n∞`.

The conformal reflection maps the algebraic origin to the point at infinity.
This is the compactification identity: spatial infinity is no longer an
unreachable limit but is mapped to a concrete algebraic element.

Proof sketch: expand `(u−v)u(u−v)`, kill three of four monomial terms
using `u² = 0`, reduce the survivor `vuv = v(uv) = v(1−vu) = v − v²u = v`.
-/
theorem J_swap_origin : J p * p.u * J p = p.v := by
  unfold J
  have hu : p.u * p.u = 0 := by rw [← sq]; exact p.u_square
  have hv : p.v * p.v = 0 := by rw [← sq]; exact p.v_square
  have huv : p.u * p.v = 1 - p.v * p.u := by
    rw [eq_sub_iff_add_eq]; exact p.anticomm
  have h1 : p.u * p.u * p.u = 0 := by rw [hu, zero_mul]
  have h2 : p.u * p.u * p.v = 0 := by rw [hu, zero_mul]
  have h3 : p.v * p.u * p.u = 0 := by rw [mul_assoc, hu, mul_zero]
  calc (p.u - p.v) * p.u * (p.u - p.v)
      = p.u * p.u * p.u - p.u * p.u * p.v
        - p.v * p.u * p.u + p.v * p.u * p.v := by noncomm_ring
    _ = 0 - 0 - 0 + p.v * p.u * p.v := by rw [h1, h2, h3]
    _ = p.v * (p.u * p.v) := by noncomm_ring
    _ = p.v * (1 - p.v * p.u) := by rw [huv]
    _ = p.v - p.v * p.v * p.u := by noncomm_ring
    _ = p.v - 0 * p.u := by rw [hv]
    _ = p.v := by noncomm_ring

/--
Sandwich swap (infinity → origin): `J · n∞ · J = n₀`.

The conformal reflection maps the point at infinity back to the algebraic
origin. Together with `J_swap_origin`, this establishes that `J` implements
the full `n₀ ↔ n∞` exchange of conformal geometric algebra.

Proof sketch: expand `(u−v)v(u−v)`, kill three of four monomial terms
using `v² = 0`, reduce the survivor `uvu = u(vu) = u(1−uv) = u − u²v = u`.
-/
theorem J_swap_infinity : J p * p.v * J p = p.u := by
  unfold J
  have hu : p.u * p.u = 0 := by rw [← sq]; exact p.u_square
  have hv : p.v * p.v = 0 := by rw [← sq]; exact p.v_square
  have hvu : p.v * p.u = 1 - p.u * p.v := by
    rw [eq_sub_iff_add_eq, add_comm]; exact p.anticomm
  have h1 : p.u * p.v * p.v = 0 := by rw [mul_assoc, hv, mul_zero]
  have h2 : p.v * p.v * p.u = 0 := by rw [hv, zero_mul]
  have h3 : p.v * p.v * p.v = 0 := by rw [hv, zero_mul]
  calc (p.u - p.v) * p.v * (p.u - p.v)
      = p.u * p.v * p.u - p.u * p.v * p.v
        - p.v * p.v * p.u + p.v * p.v * p.v := by noncomm_ring
    _ = p.u * p.v * p.u - 0 - 0 + 0 := by rw [h1, h2, h3]
    _ = p.u * (p.v * p.u) := by noncomm_ring
    _ = p.u * (1 - p.u * p.v) := by rw [hvu]
    _ = p.u - p.u * p.u * p.v := by noncomm_ring
    _ = p.u - 0 * p.v := by rw [hu]
    _ = p.u := by noncomm_ring

/-! ### Invertibility of J -/

/-- `J` is left-invertible with inverse `−J`: `J · (−J) = 1`. -/
theorem J_mul_neg_J : J p * (-J p) = 1 := by
  rw [mul_neg, ← sq, J_sq, neg_neg]

/-- `J` is right-invertible with inverse `−J`: `(−J) · J = 1`. -/
theorem neg_J_mul_J : (-J p) * J p = 1 := by
  rw [neg_mul, ← sq, J_sq, neg_neg]

/-! ### Involutivity of the sandwich swap -/

/-- Applying the sandwich swap twice on the origin returns the origin:
`J(JuJ)J = u`. -/
theorem J_swap_involutive_origin :
    J p * (J p * p.u * J p) * J p = p.u := by
  rw [J_swap_origin]
  exact J_swap_infinity p

/-- Applying the sandwich swap twice on infinity returns infinity:
`J(JvJ)J = v`. -/
theorem J_swap_involutive_infinity :
    J p * (J p * p.v * J p) * J p = p.v := by
  rw [J_swap_infinity]
  exact J_swap_origin p

end InfoGeometry.Clifford.ConformalReflection55
