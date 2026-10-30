/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.UnipotentSteinberg
import InfoGeometry.Core.PeirceDecomposition

/-!
# Peirce-corner instantiation of the square-zero pair spectral theory

For an idempotent `p` of an associative `R`-algebra `A`, the canonical
corners `u = component10 p a = p a (1 - p)` and
`v = component01 p b = (1 - p) b p` form a square-zero pair, so every result
of `SquareZeroPairSpectral` applies to them. This file records the corner
relations and the identities that genuinely involve `p`: unipotent
conjugation of `p` and of the Cartan reflection, the same-corner group law,
and two iterated-conjugation identities.

The last two correct AI-generated intake claims:
`Ad₊ Ad₋ p - Ad₋ Ad₊ p` equals `-(V Φ)` (not `2 Σ - V J`), and the
`Ad₊ Ad₋⁻¹ Ad₊` orbit of `p` is the explicit polynomial below. Both were
first checked on exact rational corner models in `Mat₅(ℚ)` and are proved
here for every associative algebra. Neither needs idempotency of `p`: the
four corner relations `p u = u`, `u p = 0`, `v p = v`, `p v = 0` suffice.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

open InfoGeometry.Core.PeirceDecomposition

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-! ### Abstract corner relations -/

section CornerPair

variable {p u v : A}

/-- Square-zero of the `10` corner from `p u = u`, `u p = 0`. -/
theorem sq_zero_of_corner10 (hpu : p * u = u) (hup : u * p = 0) : u * u = 0 := by
  calc u * u = u * (p * u) := by rw [hpu]
    _ = 0 := by rw [← mul_assoc, hup, zero_mul]

theorem sq_zero_of_corner01 (hvp : v * p = v) (hpv : p * v = 0) : v * v = 0 := by
  calc v * v = (v * p) * v := by rw [hvp]
    _ = 0 := by rw [mul_assoc, hpv, mul_zero]

/-- Right-nested form of a left-absorption rule `a * b = c`. -/
theorem mul_mul_of_mul_eq {a b c : A} (h : a * b = c) (x : A) : a * (b * x) = c * x := by
  rw [← mul_assoc, h]

/-- `Ad(1 + u) p = p - u`. -/
theorem unipotentConj_corner10_idem (hpu : p * u = u) (hup : u * p = 0) :
    unipotentConj R u p = p - u := by
  have hu := sq_zero_of_corner10 hpu hup
  rw [unipotentConj_apply]
  noncomm_ring [hpu, hup, hu, mul_mul_of_mul_eq hpu, mul_mul_of_mul_eq hup]

/-- `Ad(1 + v) p = p + v`. -/
theorem unipotentConj_corner01_idem (hvp : v * p = v) (hpv : p * v = 0) :
    unipotentConj R v p = p + v := by
  have hv := sq_zero_of_corner01 hvp hpv
  rw [unipotentConj_apply]
  noncomm_ring [hvp, hpv, hv, mul_mul_of_mul_eq hvp, mul_mul_of_mul_eq hpv]

/-- `Ad(1 + u)` shifts the Cartan reflection `2 p - 1` by `-2 u`. -/
theorem unipotentConj_corner10_reflection (hpu : p * u = u) (hup : u * p = 0) :
    unipotentConj R u ((2 : ℕ) • p - 1) = ((2 : ℕ) • p - 1) - (2 : ℕ) • u := by
  have hu := sq_zero_of_corner10 hpu hup
  rw [unipotentConj_apply, two_nsmul, two_nsmul]
  noncomm_ring [hpu, hup, hu, mul_mul_of_mul_eq hpu, mul_mul_of_mul_eq hup]

theorem unipotentConj_corner01_reflection (hvp : v * p = v) (hpv : p * v = 0) :
    unipotentConj R v ((2 : ℕ) • p - 1) = ((2 : ℕ) • p - 1) + (2 : ℕ) • v := by
  have hv := sq_zero_of_corner01 hvp hpv
  rw [unipotentConj_apply, two_nsmul, two_nsmul]
  noncomm_ring [hvp, hpv, hv, mul_mul_of_mul_eq hvp, mul_mul_of_mul_eq hpv]

/-- The commutator of the two unipotent flows on `p` is `-(V Φ)`
(correcting the intake claim `2 Σ - V J`). -/
theorem unipotentConj_corner_commutator_idem (hpu : p * u = u) (hup : u * p = 0)
    (hvp : v * p = v) (hpv : p * v = 0) :
    unipotentConj R u (unipotentConj R v p) - unipotentConj R v (unipotentConj R u p) =
      -((u * v + v * u) * (u + v)) := by
  have hu := sq_zero_of_corner10 hpu hup
  have hv := sq_zero_of_corner01 hvp hpv
  rw [unipotentConj_corner01_idem hvp hpv,
    unipotentConj_corner10_idem hpu hup, unipotentConj_apply, unipotentConj_apply]
  noncomm_ring [hpu, hup, hvp, hpv, hu, hv, mul_mul_eq_zero_of_sq hu,
    mul_mul_eq_zero_of_sq hv, mul_mul_of_mul_eq hpu, mul_mul_of_mul_eq hup,
    mul_mul_of_mul_eq hvp, mul_mul_of_mul_eq hpv]

/-- The Steinberg orbit `Ad(1 + u) Ad(1 - v) Ad(1 + u)` of `p`
(correcting the intake claim `p - J - Σ - u + 2 V u`). -/
theorem unipotentConj_corner_steinberg_idem (hpu : p * u = u) (hup : u * p = 0)
    (hvp : v * p = v) (hpv : p * v = 0) :
    unipotentConj R u (unipotentConj R (-v) (unipotentConj R u p)) =
      p - (2 : ℕ) • u - v - (2 : ℕ) • (u * v - v * u) + (3 : ℕ) • ((u * v + v * u) * u) +
        (u * v + v * u) * v + (u * v + v * u) * (u * v - v * u) -
        (u * v + v * u) * (u * v + v * u) * u := by
  have hu := sq_zero_of_corner10 hpu hup
  have hv := sq_zero_of_corner01 hvp hpv
  rw [unipotentConj_corner10_idem hpu hup, unipotentConj_apply, unipotentConj_apply]
  simp only [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul]
  noncomm_ring [hpu, hup, hvp, hpv, hu, hv, mul_mul_eq_zero_of_sq hu,
    mul_mul_eq_zero_of_sq hv, mul_mul_of_mul_eq hpu, mul_mul_of_mul_eq hup,
    mul_mul_of_mul_eq hvp, mul_mul_of_mul_eq hpv]

end CornerPair

/-! ### The canonical corners `component10 p a`, `component01 p b` -/

section Components

variable {p : A} (hp : p * p = p) (a b : A)
include hp

theorem idem_mul_component10 : p * component10 p a = component10 p a := by
  simp only [component10, complementIdempotent]
  noncomm_ring [hp, mul_mul_of_mul_eq hp]

theorem component10_mul_idem : component10 p a * p = 0 := by
  simp only [component10, complementIdempotent]
  noncomm_ring [hp, mul_mul_of_mul_eq hp]

theorem component01_mul_idem : component01 p b * p = component01 p b := by
  simp only [component01, complementIdempotent]
  noncomm_ring [hp, mul_mul_of_mul_eq hp]

theorem idem_mul_component01 : p * component01 p b = 0 := by
  simp only [component01, complementIdempotent]
  noncomm_ring [hp, mul_mul_of_mul_eq hp]

theorem component10_sq_zero : component10 p a * component10 p a = 0 :=
  sq_zero_of_corner10 (idem_mul_component10 hp a) (component10_mul_idem hp a)

theorem component01_sq_zero : component01 p b * component01 p b = 0 :=
  sq_zero_of_corner01 (component01_mul_idem hp b) (idem_mul_component01 hp b)

/-- Same-corner operators annihilate each other, hence their unipotent
conjugations form an additive one-parameter group. -/
theorem component10_mul_component10 (a' : A) :
    component10 p a * component10 p a' = 0 := by
  calc component10 p a * component10 p a'
      = component10 p a * (p * component10 p a') := by rw [idem_mul_component10 hp]
    _ = 0 := by rw [← mul_assoc, component10_mul_idem hp, zero_mul]

theorem unipotentConj_component10_add (a' : A) :
    unipotentConj R (component10 p a) * unipotentConj R (component10 p a') =
      unipotentConj R (component10 p a + component10 p a') :=
  unipotentConj_mul_of_annihilate (component10_mul_component10 hp a a')
    (component10_mul_component10 hp a' a)

/-- The corrected Steinberg orbit of `p` for the canonical corners. -/
theorem component_steinberg_idem :
    unipotentConj R (component10 p a)
        (unipotentConj R (-component01 p b) (unipotentConj R (component10 p a) p)) =
      p - (2 : ℕ) • component10 p a - component01 p b -
        (2 : ℕ) • (component10 p a * component01 p b - component01 p b * component10 p a) +
        (3 : ℕ) • ((component10 p a * component01 p b + component01 p b * component10 p a) *
          component10 p a) +
        (component10 p a * component01 p b + component01 p b * component10 p a) *
          component01 p b +
        (component10 p a * component01 p b + component01 p b * component10 p a) *
          (component10 p a * component01 p b - component01 p b * component10 p a) -
        (component10 p a * component01 p b + component01 p b * component10 p a) *
          (component10 p a * component01 p b + component01 p b * component10 p a) *
          component10 p a :=
  unipotentConj_corner_steinberg_idem (idem_mul_component10 hp a)
    (component10_mul_idem hp a) (component01_mul_idem hp b) (idem_mul_component01 hp b)

/-- The corrected commutator of the two corner flows on `p`. -/
theorem component_commutator_idem :
    unipotentConj R (component10 p a) (unipotentConj R (component01 p b) p) -
        unipotentConj R (component01 p b) (unipotentConj R (component10 p a) p) =
      -((component10 p a * component01 p b + component01 p b * component10 p a) *
        (component10 p a + component01 p b)) :=
  unipotentConj_corner_commutator_idem (idem_mul_component10 hp a)
    (component10_mul_idem hp a) (component01_mul_idem hp b) (idem_mul_component01 hp b)

end Components

end InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral
