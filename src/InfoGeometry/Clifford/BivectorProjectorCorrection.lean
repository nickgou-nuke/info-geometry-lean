import InfoGeometry.Clifford.ThreeDHurwitz
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Bivector projectors: what is true, and what is not

## Why this module exists

A common claim in geometric-algebra write-ups is that the uninterpreted scalar
imaginary unit `i` may be *replaced* by an oriented unit 2-blade `I`, and that the
circular/chiral projectors may then be written as `½(1 ± I)`.  This module exists
because that claim is **false as stated**, and the failure is worth pinning down
precisely rather than leaving as a prose caveat.

The genuine content — the unit 2-blade squaring to `-1`, and the two `90°`
identities — is already owned by `InfoGeometry.Clifford.ThreeDHurwitz`
(`bivector01_sq`).  Nothing here rebuilds it.  What was missing is the layer that
distinguishes a *bivector* projector from a *vector* projector, and that refutes
the substitution.  That layer is what this file supplies.

## The carrier

`Cl` below is `Cl(3,0)`, the Clifford algebra of the **definite** form
`Qdiag3 1 1 1`, with generators `g0, g1, g2` satisfying `gᵢ² = 1` and
`gᵢgⱼ = -gⱼgᵢ`.  `unitBivector = g0 g1` is the unit 2-blade of the
`g0 g1`-plane.

## What is proved

1. `unitBivector_sq` — `(g0 g1)² = -1`.  True, and it is the reason a bivector can
   play the algebraic role of `√-1`.
2. `g0_mul_unitBivector`, `g1_mul_unitBivector` — `g0 I = g1` and `g1 I = -g0`:
   multiplication by `I` rotates the plane by `90°`.  True.
3. `one_add_unitBivector_sq` — **`(1 + I)² = 2I`.**  Note carefully: `2I`, not
   `2(1 + I)`.  This single identity is the whole refutation.
4. `idem_forces_two_eq_zero` and `two_ne_zero` together rule out the numerator
   identity `(1 + I)² = 2(1 + I)`.  `vectorProjector_idempotent` contrasts the
   `v² = +1` case with the bivector relation `I² = -1`.  The normalized
   scalar–bivector model has the same obstruction by direct coordinate
   expansion.
5. `g0_sub_g1_sq` proves `(g0 - g1)² = 2`; the unscaled difference is not null
   in this positive-definite Clifford algebra.  No statement about a complex
   circular basis or a normalized difference is made here.

## Scope of the obstruction

This file proves that `½(1 ± I)` is not an idempotent construction when the
real Clifford element satisfies `I² = -1`, and that the real vector expression
`½(1 ± v)` is idempotent when `v² = 1`.  It does not define a real-algebra
equivalence with `Mat₂(ℂ)` or identify the preimage of any complex Pauli
projector.  Such a correspondence needs an explicit algebra map and cannot be
inferred merely by replacing the symbol `i` with a blade.
-/

namespace InfoGeometry.Clifford.BivectorProjector

open InfoGeometry.Clifford.ThreeDHurwitz

/-- `Cl(3,0)`: the Clifford algebra of the definite form `Qdiag3 1 1 1`. -/
abbrev Cl := Cl3 1 1 1

/-- The unit 2-blade of the `g0 g1`-plane: `I = g₀ ∧ g₁`. -/
noncomputable def unitBivector : Cl := g0 1 1 1 * g1 1 1 1

/-- **The unit 2-blade squares to `-1`.**  This is the algebraic reason a bivector
can serve as a real `√-1`; inherited from `ThreeDHurwitz.bivector01_sq`. -/
theorem unitBivector_sq : unitBivector * unitBivector = -(1 : Cl) := by
  have h := bivector01_sq (s0 := 1) (s1 := 1) (s2 := 1)
  simpa [unitBivector] using h

/-- **Multiplication by the unit bivector is a `90°` rotation of the plane:**
`g₀ I = g₁`. -/
theorem g0_mul_unitBivector : g0 1 1 1 * unitBivector = g1 1 1 1 := by
  rw [unitBivector, ← mul_assoc, g0_sq (s0 := 1) (s1 := 1) (s2 := 1)]
  simp

/-- ...and `g₁ I = -g₀`. -/
theorem g1_mul_unitBivector : g1 1 1 1 * unitBivector = -(g0 1 1 1) := by
  have hswap : g1 1 1 1 * g0 1 1 1 = -(g0 1 1 1 * g1 1 1 1) := by
    rw [g0_g1_anti]
    simp
  rw [unitBivector]
  calc
    g1 1 1 1 * (g0 1 1 1 * g1 1 1 1) =
        (g1 1 1 1 * g0 1 1 1) * g1 1 1 1 := by rw [mul_assoc]
    _ = -(g0 1 1 1 * g1 1 1 1) * g1 1 1 1 := by rw [hswap]
    _ = -(g0 1 1 1 * (g1 1 1 1 * g1 1 1 1)) := by rw [← mul_assoc, neg_mul]
    _ = -(g0 1 1 1) := by
      rw [g1_sq (s0 := 1) (s1 := 1) (s2 := 1)]
      simp

/-! ## The projector obstruction for `I² = -1` -/

/-- **The square of `1 + I` is `2I`, not `2(1 + I)`.**  Expand and use `I² = -1`:
`1 + 2I + I² = 1 + 2I - 1 = 2I`. -/
theorem one_add_unitBivector_sq :
    (1 + unitBivector) * (1 + unitBivector) = 2 * unitBivector := by
  simp only [mul_add, add_mul, one_mul, mul_one]
  rw [unitBivector_sq]
  noncomm_ring

/-- The same identity for the minus sign. -/
theorem one_sub_unitBivector_sq :
    (1 - unitBivector) * (1 - unitBivector) = -(2 * unitBivector) := by
  simp only [mul_sub, sub_mul, one_mul, mul_one]
  rw [unitBivector_sq]
  noncomm_ring

/-- If the numerator `1 + I` satisfied the projector-scaled identity, then `2 = 0`. -/
theorem idem_forces_two_eq_zero
    (h : (1 + unitBivector) * (1 + unitBivector) = 2 * (1 + unitBivector)) :
    (2 : Cl) = 0 := by
  rw [one_add_unitBivector_sq] at h
  have h' : 2 * unitBivector = 2 + 2 * unitBivector := by
    calc
      2 * unitBivector = 2 * (1 + unitBivector) := h
      _ = 2 + 2 * unitBivector := by
        rw [two_mul (1 + unitBivector), two_mul unitBivector]
        have htwo : (2 : Cl) = 1 + 1 := by norm_num
        rw [htwo]
        ac_rfl
  have hcancel := congrArg (fun x : Cl => x - 2 * unitBivector) h'
  have htwo : (2 : Cl) = 0 := by
    calc
      (2 : Cl) = (2 + 2 * unitBivector) - 2 * unitBivector := by noncomm_ring
      _ = 0 := by simpa using hcancel.symm
  exact htwo

/-- The scalar `2` remains nonzero in this real Clifford algebra. -/
theorem two_ne_zero : (2 : Cl) ≠ 0 := by
  intro h
  have hmap : algebraMap ℝ Cl (2 : ℝ) = algebraMap ℝ Cl (0 : ℝ) := by
    simpa only [map_ofNat, map_zero] using h
  have hreal : (2 : ℝ) = 0 := (algebraMap ℝ Cl).injective hmap
  norm_num at hreal

/-- Consequently the numerator `1 + I` is not idempotent.  For the normalized
real scalar–bivector projector expression, see the coordinate rotor owner. -/
theorem one_add_unitBivector_not_idempotent :
    (1 + unitBivector) * (1 + unitBivector) ≠ 2 * (1 + unitBivector) := by
  intro h
  exact two_ne_zero (idem_forces_two_eq_zero h)

theorem one_sub_unitBivector_not_idempotent :
    (1 - unitBivector) * (1 - unitBivector) ≠ 2 * (1 - unitBivector) := by
  intro h
  rw [one_sub_unitBivector_sq] at h
  have h' : -(2 * unitBivector) = 2 - 2 * unitBivector := by
    calc
      -(2 * unitBivector) = 2 * (1 - unitBivector) := h
      _ = 2 - 2 * unitBivector := by
        rw [mul_sub, mul_one]
  have hzero : (0 : Cl) = 2 := by
    calc
      (0 : Cl) = -(2 * unitBivector) + 2 * unitBivector := by noncomm_ring
      _ = (2 - 2 * unitBivector) + 2 * unitBivector := by rw [h']
      _ = 2 := by noncomm_ring
  exact two_ne_zero hzero.symm

/-- The projector identity that *does* hold for a unit **vector**.  This is the
statement the bivector version was mistaken for. -/
theorem vectorProjector_idempotent (v : Cl) (hv : v * v = 1) :
    (1 + v) * (1 + v) = 2 * (1 + v) := by
  simp only [mul_add, add_mul, one_mul, mul_one, hv]
  rw [two_mul v]
  have htwo : (2 : Cl) = 1 + 1 := by norm_num
  rw [htwo]
  ac_rfl

/-- Instantiating at `v = g₀`: `½(1 + g₀)` is a genuine idempotent. -/
theorem g0_projector_idempotent :
    (1 + g0 1 1 1) * (1 + g0 1 1 1) = 2 * (1 + g0 1 1 1) := by
  apply vectorProjector_idempotent
  exact g0_sq (s0 := 1) (s1 := 1) (s2 := 1)

/-! ## The refutation: the "circular basis vectors" are not null -/

/-- The unscaled difference has square `2`, so it is not a null Clifford element. -/
theorem g0_sub_g1_sq :
    (g0 1 1 1 - g1 1 1 1) * (g0 1 1 1 - g1 1 1 1) = (2 : Cl) := by
  simp only [mul_sub, sub_mul]
  rw [g0_sq (s0 := 1) (s1 := 1) (s2 := 1), g1_sq (s0 := 1) (s1 := 1) (s2 := 1),
    g0_g1_anti (s0 := 1) (s1 := 1) (s2 := 1)]
  noncomm_ring
  simp

/-- The difference is non-null, using the nonzero scalar theorem above. -/
theorem g0_sub_g1_not_null :
    (g0 1 1 1 - g1 1 1 1) * (g0 1 1 1 - g1 1 1 1) ≠ 0 := by
  rw [g0_sub_g1_sq]
  exact two_ne_zero

end InfoGeometry.Clifford.BivectorProjector
