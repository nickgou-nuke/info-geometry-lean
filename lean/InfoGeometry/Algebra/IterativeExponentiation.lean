import Mathlib.Tactic

/-!
# Iterative exponentiation

This file records the non-analytic exponentiation lane used by finite induction
arguments: powers and iterated products are defined by primitive recursion.

This is not a Taylor series, not an infinite sum, and not an analytic
completion.  Each value at depth `n` is obtained by exactly `n` finite
multiplication steps.
-/

namespace InfoGeometry.Algebra.IterativeExponentiation

universe u v

section Powers

variable {M : Type u} [Monoid M]

/-- Primitive-recursive exponentiation by a natural number. -/
def inductivePower (x : M) : ℕ → M
  | 0 => 1
  | n + 1 => inductivePower x n * x

@[simp]
theorem inductivePower_zero (x : M) :
    inductivePower x 0 = 1 := by
  rfl

@[simp]
theorem inductivePower_succ (x : M) (n : ℕ) :
    inductivePower x (n + 1) = inductivePower x n * x := by
  rfl

/-- The recursive definition agrees with Lean's standard finite power. -/
theorem inductivePower_eq_pow (x : M) :
    ∀ n : ℕ, inductivePower x n = x ^ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [inductivePower_succ, ih, pow_succ]

/-- Recursive powers multiply by adding exponents. -/
theorem inductivePower_add (x : M) (m n : ℕ) :
    inductivePower x (m + n) = inductivePower x m * inductivePower x n := by
  rw [inductivePower_eq_pow, inductivePower_eq_pow, inductivePower_eq_pow, pow_add]

variable {N : Type v} [Monoid N]

/-- Monoid homomorphisms preserve primitive-recursive powers. -/
theorem map_inductivePower (f : M →* N) (x : M) :
    ∀ n : ℕ, f (inductivePower x n) = inductivePower (f x) n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [ih]

end Powers

section IterativeProducts

variable {M : Type u} [Monoid M]

/-- Product of the first `n` terms of a time-dependent multiplicative process. -/
def iterativeProduct (step : ℕ → M) : ℕ → M
  | 0 => 1
  | n + 1 => iterativeProduct step n * step n

@[simp]
theorem iterativeProduct_zero (step : ℕ → M) :
    iterativeProduct step 0 = 1 := by
  rfl

@[simp]
theorem iterativeProduct_succ (step : ℕ → M) (n : ℕ) :
    iterativeProduct step (n + 1) = iterativeProduct step n * step n := by
  rfl

/-- Constant-step iterative products are primitive-recursive powers. -/
theorem iterativeProduct_const (x : M) :
    ∀ n : ℕ, iterativeProduct (fun _ => x) n = inductivePower x n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [ih]

variable {N : Type v} [Monoid N]

/-- Monoid homomorphisms preserve finite iterative products. -/
theorem map_iterativeProduct (f : M →* N) (step : ℕ → M) :
    ∀ n : ℕ, f (iterativeProduct step n) = iterativeProduct (fun k => f (step k)) n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [ih]

end IterativeProducts

section Orbits

variable {α : Type u}

/-- Primitive-recursive orbit of a self-map. -/
def iterativeOrbit (step : α → α) (x0 : α) : ℕ → α
  | 0 => x0
  | n + 1 => step (iterativeOrbit step x0 n)

@[simp]
theorem iterativeOrbit_zero (step : α → α) (x0 : α) :
    iterativeOrbit step x0 0 = x0 := by
  rfl

@[simp]
theorem iterativeOrbit_succ (step : α → α) (x0 : α) (n : ℕ) :
    iterativeOrbit step x0 (n + 1) = step (iterativeOrbit step x0 n) := by
  rfl

/-- Any sequence satisfying the same seed and successor equation is the iterative orbit. -/
theorem iterativeOrbit_unique
    (step : α → α) (x0 : α) (y : ℕ → α)
    (hy0 : y 0 = x0)
    (hysucc : ∀ n : ℕ, y (n + 1) = step (y n)) :
    ∀ n : ℕ, y n = iterativeOrbit step x0 n := by
  intro n
  induction n with
  | zero =>
      exact hy0
  | succ n ih =>
      rw [hysucc n, iterativeOrbit_succ, ih]

/-- Invariants of finite iterative orbits are proved by induction. -/
theorem invariant_iterativeOrbit
    {I : α → Prop} {step : α → α} {x0 : α}
    (h0 : I x0)
    (hstep : ∀ n : ℕ, I (iterativeOrbit step x0 n) →
      I (step (iterativeOrbit step x0 n))) :
    ∀ n : ℕ, I (iterativeOrbit step x0 n) := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      simpa using hstep n ih

end Orbits

end InfoGeometry.Algebra.IterativeExponentiation
