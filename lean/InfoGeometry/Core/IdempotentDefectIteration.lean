/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentGraphGrassmannian
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Finite iteration of the idempotency defect

Orthogonality in each multiplication order persists under the defect map.
Consequently every finite iterate splits across mutually orthogonal inputs.
Ring homomorphisms transport the entire finite orbit.

The existing Newton–Peirce correction also terminates after `n` steps whenever
the initial defect is annihilated by the power `2 ^ n`. This finite algebraic
result preserves ordered intertwiners and requires no topology or
commutativity of the ambient ring. Raw defect iteration and corrective Newton
iteration are distinct functions.
-/

namespace InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B C : Type*} [Ring B] [Ring C]

/-- One Newton–Peirce correction for the idempotency equation. -/
def newtonPeirceStep (x : B) : B := 3 * x * x - 2 * x * x * x

/-- The defect after one Newton–Peirce step factors as a polynomial in the
original defect. The factor order is stated explicitly; all factors are
polynomials in the same element. -/
theorem idempotencyDefect_newtonPeirceStep (x : B) :
    idempotencyDefect (newtonPeirceStep x) =
      idempotencyDefect x * idempotencyDefect x *
        (4 * idempotencyDefect x - 3) := by
  unfold idempotencyDefect newtonPeirceStep
  noncomm_ring

/-- A square-zero idempotency defect is corrected to an exact idempotent in
one Newton–Peirce step, over any associative ring. This hypothesis is about
`x² - x`, not about nilpotence of `x` itself. -/
theorem newtonPeirceStep_idempotent_of_defect_sq_zero {x : B}
    (hδ : idempotencyDefect x * idempotencyDefect x = 0) :
    newtonPeirceStep x * newtonPeirceStep x = newtonPeirceStep x := by
  apply (idempotencyDefect_eq_zero_iff).mp
  rw [idempotencyDefect_newtonPeirceStep, hδ]
  simp

/-- The Newton–Peirce correction fixes an exact idempotent. -/
theorem newtonPeirceStep_eq_self_of_idempotent {x : B}
    (hx : x * x = x) : newtonPeirceStep x = x := by
  unfold newtonPeirceStep
  noncomm_ring [hx]

/-- A commuting square-zero perturbation is removed in one polynomial step.
This is exact finite termination in the original associative ring, without
division or an analytic limiting process. -/
theorem newtonPeirceStep_add_commuting_square_zero {p n : B}
    (hp : p * p = p) (hn : n * n = 0) (hpn : Commute p n) :
    newtonPeirceStep (p + n) = p := by
  have hpp (x : B) : p * (p * x) = p * x := by rw [← mul_assoc, hp]
  have hnn (x : B) : n * (n * x) = 0 := by rw [← mul_assoc, hn, zero_mul]
  unfold newtonPeirceStep
  noncomm_ring [hp, hn, hpn.eq, hpp, hnn]

/-- On two-sided orthogonal inputs, the Newton–Peirce polynomial is additive:
every mixed quadratic and cubic monomial vanishes. -/
theorem newtonPeirceStep_add_of_orthogonal {x y : B}
    (hxy : x * y = 0) (hyx : y * x = 0) :
    newtonPeirceStep (x + y) = newtonPeirceStep x + newtonPeirceStep y := by
  unfold newtonPeirceStep
  noncomm_ring [hxy, hyx]

/-- One-sided annihilation suffices for the ordered product of defects. -/
theorem idempotencyDefect_mul_eq_zero {x y : B} (hxy : x * y = 0) :
    idempotencyDefect x * idempotencyDefect y = 0 := by
  have h : x * (y * y) = 0 := by rw [← mul_assoc, hxy, zero_mul]
  simp only [idempotencyDefect, sub_mul, mul_sub, mul_assoc, h, hxy,
    mul_zero, sub_self]

theorem idempotencyDefect_iterates_mul_eq_zero {x y : B}
    (hxy : x * y = 0) (n : ℕ) :
    idempotencyDefect^[n] x * idempotencyDefect^[n] y = 0 := by
  induction n with
  | zero => exact hxy
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact idempotencyDefect_mul_eq_zero ih

/-- The full finite defect orbit splits over orthogonal ring elements. -/
theorem idempotencyDefect_iterates_add_of_orthogonal {x y : B}
    (hxy : x * y = 0) (hyx : y * x = 0) (n : ℕ) :
    idempotencyDefect^[n] (x + y) =
      idempotencyDefect^[n] x + idempotencyDefect^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih]
    exact idempotencyDefect_add_of_orthogonal
      (idempotencyDefect_iterates_mul_eq_zero hxy n)
      (idempotencyDefect_iterates_mul_eq_zero hyx n)

theorem map_idempotencyDefect_iterates (f : B →+* C) (x : B) (n : ℕ) :
    f (idempotencyDefect^[n] x) = idempotencyDefect^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', map_idempotencyDefect, ih]

/-- The defect polynomial transports an operator intertwining equation. -/
theorem idempotencyDefect_intertwines {x y z : B} (h : x * y = y * z) :
    idempotencyDefect x * y = y * idempotencyDefect z := by
  unfold idempotencyDefect
  calc
    (x * x - x) * y = x * (x * y) - x * y := by noncomm_ring
    _ = x * (y * z) - y * z := by rw [h]
    _ = (x * y) * z - y * z := by rw [mul_assoc]
    _ = (y * z) * z - y * z := by rw [h]
    _ = y * (z * z - z) := by noncomm_ring

/-- Every finite iterate preserves the same intertwiner, without commutativity. -/
theorem idempotencyDefect_iterates_intertwines {x y z : B}
    (h : x * y = y * z) (n : ℕ) :
    idempotencyDefect^[n] x * y = y * idempotencyDefect^[n] z := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact idempotencyDefect_intertwines ih

/-- Any two finite iterates of the same element under the idempotency-defect
polynomial commute. This uses polynomial closure, not commutativity of `B`. -/
theorem idempotencyDefect_iterates_commute (x : B) (n m : ℕ) :
    idempotencyDefect^[n] x * idempotencyDefect^[m] x =
      idempotencyDefect^[m] x * idempotencyDefect^[n] x := by
  have hSeed : x * idempotencyDefect^[n] x =
      idempotencyDefect^[n] x * x := by
    exact (idempotencyDefect_iterates_intertwines
      (x := x) (y := x) (z := x) rfl n).symm
  exact (idempotencyDefect_iterates_intertwines
    (x := x) (y := idempotencyDefect^[n] x) (z := x) hSeed m).symm

/-- Left support survives every finite defect iterate. -/
theorem idempotencyDefect_iterates_left_support {p x : B}
    (h : p * x = x) (n : ℕ) : p * idempotencyDefect^[n] x =
      idempotencyDefect^[n] x := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply', idempotencyDefect, mul_sub,
      ← mul_assoc, ih]

/-- Right support survives every finite defect iterate. -/
theorem idempotencyDefect_iterates_right_support {p x : B}
    (h : x * p = x) (n : ℕ) : idempotencyDefect^[n] x * p =
      idempotencyDefect^[n] x := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply', idempotencyDefect, sub_mul,
      mul_assoc, ih]

/-! ## Transport of Newton correction -/

/-- The existing correction polynomial is natural under unital ring maps. -/
theorem map_newtonPeirceStep (f : B →+* C) (x : B) :
    f (newtonPeirceStep x) = newtonPeirceStep (f x) := by
  simp only [newtonPeirceStep, map_sub, map_mul, map_ofNat]

/-- Ring maps transport every finite corrective iterate. -/
theorem map_newtonPeirceStep_iterates (f : B →+* C) (x : B) (n : ℕ) :
    f (newtonPeirceStep^[n] x) = newtonPeirceStep^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', map_newtonPeirceStep, ih]

/-- The correction respects the order of an arbitrary intertwining equation.
The two operators and the intertwiner are not assumed to commute. -/
theorem newtonPeirceStep_intertwines {x y z : B} (h : x * y = y * z) :
    newtonPeirceStep x * y = y * newtonPeirceStep z := by
  have h₂ : x * x * y = y * (z * z) := by
    calc
      x * x * y = x * (x * y) := mul_assoc _ _ _
      _ = x * (y * z) := by rw [h]
      _ = (x * y) * z := (mul_assoc _ _ _).symm
      _ = y * (z * z) := by rw [h, mul_assoc]
  have h₃ : x * x * x * y = y * (z * z * z) := by
    calc
      x * x * x * y = x * (x * x * y) := by simp only [mul_assoc]
      _ = x * (y * (z * z)) := by rw [h₂]
      _ = (x * y) * (z * z) := (mul_assoc _ _ _).symm
      _ = y * (z * z * z) := by rw [h]; simp only [mul_assoc]
  calc
    newtonPeirceStep x * y = 3 * (x * x * y) - 2 * (x * x * x * y) := by
      unfold newtonPeirceStep
      noncomm_ring
    _ = 3 * (y * (z * z)) - 2 * (y * (z * z * z)) := by rw [h₂, h₃]
    _ = y * newtonPeirceStep z := by
      unfold newtonPeirceStep
      noncomm_ring

/-- Every corrective iterate retains the original ordered intertwiner. -/
theorem newtonPeirceStep_iterates_intertwines {x y z : B}
    (h : x * y = y * z) (n : ℕ) :
    newtonPeirceStep^[n] x * y = y * newtonPeirceStep^[n] z := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact newtonPeirceStep_intertwines ih

/-- The same correction treats the two complementary sectors compatibly. -/
theorem newtonPeirceStep_one_sub (x : B) :
    newtonPeirceStep (1 - x) = 1 - newtonPeirceStep x := by
  unfold newtonPeirceStep
  noncomm_ring

/-- Complementation commutes with every finite corrective iterate. -/
theorem newtonPeirceStep_iterates_one_sub (x : B) (n : ℕ) :
    newtonPeirceStep^[n] (1 - x) = 1 - newtonPeirceStep^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih, newtonPeirceStep_one_sub]

/-! ## Finite termination of Newton correction -/

/-- The exact defect factorization persists under every natural power. The
two factors commute because both are polynomials in the initial defect. -/
theorem idempotencyDefect_newtonPeirceStep_pow (x : B) (k : ℕ) :
    idempotencyDefect (newtonPeirceStep x) ^ k =
      idempotencyDefect x ^ (2 * k) *
        (4 * idempotencyDefect x - 3) ^ k := by
  have hcomm : Commute (idempotencyDefect x * idempotencyDefect x)
      (4 * idempotencyDefect x - 3) := by
    change (idempotencyDefect x * idempotencyDefect x) *
        (4 * idempotencyDefect x - 3) =
      (4 * idempotencyDefect x - 3) *
        (idempotencyDefect x * idempotencyDefect x)
    noncomm_ring
  rw [idempotencyDefect_newtonPeirceStep, hcomm.mul_pow,
    ← pow_two, ← pow_mul]

/-- After `n` corrections, a defect killed by the power `2 ^ n` has been
eliminated exactly. This proves a finite iteration bound in any ring. -/
theorem newtonPeirceStep_iterates_idempotent_of_defect_pow_two_pow_eq_zero
    (n : ℕ) {x : B} (hδ : idempotencyDefect x ^ (2 ^ n) = 0) :
    newtonPeirceStep^[n] x * newtonPeirceStep^[n] x =
      newtonPeirceStep^[n] x := by
  induction n generalizing x with
  | zero =>
    exact idempotencyDefect_eq_zero_iff.mp (by simpa using hδ)
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    apply ih
    rw [idempotencyDefect_newtonPeirceStep_pow]
    have hpow : idempotencyDefect x ^ (2 * 2 ^ n) = 0 := by
      simpa only [pow_succ, Nat.mul_comm] using hδ
    rw [hpow, zero_mul]

/-- Any supplied nilpotence exponent gives the explicit sufficient bound
`m ≤ 2 ^ n` on the number of Newton–Peirce corrections. -/
theorem newtonPeirceStep_iterates_idempotent_of_defect_pow_eq_zero
    {x : B} {m n : ℕ} (hδ : idempotencyDefect x ^ m = 0)
    (hmn : m ≤ 2 ^ n) :
    newtonPeirceStep^[n] x * newtonPeirceStep^[n] x =
      newtonPeirceStep^[n] x := by
  exact newtonPeirceStep_iterates_idempotent_of_defect_pow_two_pow_eq_zero
    n (pow_eq_zero_of_le hmn hδ)

/-- Once the nilpotent defect has been eliminated, every later correction
fixes the resulting idempotent. -/
theorem newtonPeirceStep_iterates_stable_of_defect_pow_eq_zero
    {x : B} {m n : ℕ} (hδ : idempotencyDefect x ^ m = 0)
    (hmn : m ≤ 2 ^ n) (k : ℕ) :
    newtonPeirceStep^[n + k] x = newtonPeirceStep^[n] x := by
  rw [Nat.add_comm n k, Function.iterate_add_apply]
  exact Function.iterate_fixed
    (newtonPeirceStep_eq_self_of_idempotent
      (newtonPeirceStep_iterates_idempotent_of_defect_pow_eq_zero hδ hmn)) k

/-- Nilpotence of the initial defect guarantees a finite stationary
idempotent. The witness is a natural-number iteration depth, with no topology
or limiting construction. -/
theorem newtonPeirceStep_eventually_idempotent_of_isNilpotent_defect
    {x : B} (hδ : IsNilpotent (idempotencyDefect x)) :
    ∃ n : ℕ,
      newtonPeirceStep^[n] x * newtonPeirceStep^[n] x =
          newtonPeirceStep^[n] x ∧
        ∀ k : ℕ, newtonPeirceStep^[n + k] x = newtonPeirceStep^[n] x := by
  obtain ⟨m, hm⟩ := hδ
  have hbound : m ≤ 2 ^ m := Nat.le_of_lt m.lt_two_pow_self
  exact ⟨m, newtonPeirceStep_iterates_idempotent_of_defect_pow_eq_zero hm hbound,
    fun k => newtonPeirceStep_iterates_stable_of_defect_pow_eq_zero hm hbound k⟩

/-- An explicit lift of an idempotent image: the corrected element is
idempotent and has exactly the same image. No section of `f` or existential
choice of a lift is required; the input `x` is the specified initial lift. -/
theorem newtonPeirceStep_iterates_lifts_idempotent
    (f : B →+* C) {x : B} {m n : ℕ}
    (hδ : idempotencyDefect x ^ m = 0) (hmn : m ≤ 2 ^ n)
    (himage : f x * f x = f x) :
    newtonPeirceStep^[n] x * newtonPeirceStep^[n] x =
        newtonPeirceStep^[n] x ∧
      f (newtonPeirceStep^[n] x) = f x := by
  refine ⟨newtonPeirceStep_iterates_idempotent_of_defect_pow_eq_zero hδ hmn, ?_⟩
  rw [map_newtonPeirceStep_iterates]
  exact Function.iterate_fixed (newtonPeirceStep_eq_self_of_idempotent himage) n

end InfoGeometry.Core.IdempotentGraphGrassmannian
