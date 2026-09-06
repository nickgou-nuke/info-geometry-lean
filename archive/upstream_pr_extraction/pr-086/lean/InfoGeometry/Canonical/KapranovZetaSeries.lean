import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Cauchy Series and Kapranov Zeta Multiplicativity

This file formalizes the finite algebraic core of the Kapranov motivic zeta
function multiplicativity argument.  It uses formal series as coefficient
functions `Nat → R` with Cauchy convolution multiplication.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `cauchyMul_apply`, `oneSeries_apply`, `mul_one_series`,
  `cauchyMul_comm`, `mul_comm_series`, `geometricSeries_apply`,
  `linearFactor_apply`, `linearFactor_mul_geometricSeries`,
  `quadraticFactor_apply`, `linearFactor_mul_linearFactor`,
  `mot_zeta_mult`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  `mot_zeta_mult` is conditional on the coefficientwise convolution relation
  for the supplied symmetric-power coefficient function.
- BUCKET 3: OPEN CLOSURE DEBT:
  The Grothendieck ring of algebraic varieties, geometric symmetric products,
  and the geometric proof of the symmetric-power scissor relation are not
  asserted here.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.KapranovZetaSeries

/-- A formal series with coefficients in `R`, represented by its coefficient function. -/
abbrev Series (R : Type u) :=
  ℕ → R

/-- Cauchy convolution product of formal series. -/
def cauchyMul {R : Type*} [Semiring R] (f g : Series R) : Series R :=
  fun n => Finset.sum (Finset.range (n + 1)) (fun i => f i * g (n - i))

instance instMul {R : Type*} [Semiring R] : Mul (Series R) where
  mul := cauchyMul

/-- The multiplicative identity series. -/
def oneSeries {R : Type*} [Semiring R] : Series R :=
  fun n => if n = 0 then 1 else 0

instance instOne {R : Type*} [Semiring R] : One (Series R) where
  one := oneSeries

@[simp]
theorem cauchyMul_apply {R : Type*} [Semiring R] (f g : Series R) (n : ℕ) :
    cauchyMul f g n = Finset.sum (Finset.range (n + 1)) (fun i => f i * g (n - i)) :=
  rfl

@[simp]
theorem oneSeries_apply {R : Type*} [Semiring R] (n : ℕ) :
    (oneSeries : Series R) n = if n = 0 then 1 else 0 :=
  rfl

/-- Right multiplication by the identity series leaves any formal series unchanged. -/
theorem mul_one_series {R : Type*} [Semiring R] (f : Series R) :
    f * 1 = f := by
  funext n
  change cauchyMul f oneSeries n = f n
  rw [cauchyMul_apply]
  rw [Finset.sum_range_succ]
  have h_sum :
      Finset.sum (Finset.range n) (fun i => f i * oneSeries (n - i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    have h_ne : n - i ≠ 0 := by omega
    simp [oneSeries, h_ne]
  rw [h_sum, zero_add]
  simp [oneSeries]

/-- Cauchy convolution is commutative over a commutative coefficient semiring. -/
theorem cauchyMul_comm {R : Type*} [CommSemiring R] (f g : Series R) :
    cauchyMul f g = cauchyMul g f := by
  funext n
  rw [cauchyMul_apply, cauchyMul_apply]
  rw [← Finset.sum_range_reflect (fun i => g i * f (n - i)) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have h_reflect : n + 1 - 1 - i = n - i := by omega
  have h_sub : n - (n - i) = i := by omega
  rw [h_reflect, h_sub]
  exact mul_comm (f i) (g (n - i))

/-- Series multiplication is commutative over a commutative coefficient semiring. -/
theorem mul_comm_series {R : Type*} [CommSemiring R] (f g : Series R) :
    f * g = g * f :=
  cauchyMul_comm f g

/-- Formal geometric series with coefficient `c^n`. -/
def geometricSeries {R : Type*} [Monoid R] (c : R) : Series R :=
  fun n => c ^ n

/-- The linear factor `1 - cT` as a formal series. -/
def linearFactor {R : Type*} [Ring R] (c : R) : Series R :=
  fun n => if n = 0 then 1 else if n = 1 then -c else 0

@[simp]
theorem geometricSeries_apply {R : Type*} [Monoid R] (c : R) (n : ℕ) :
    geometricSeries c n = c ^ n :=
  rfl

@[simp]
theorem linearFactor_apply {R : Type*} [Ring R] (c : R) (n : ℕ) :
    linearFactor c n = if n = 0 then 1 else if n = 1 then -c else 0 :=
  rfl

/-- The finite Cauchy-coefficient proof that `(1 - cT) * (1 + cT + c^2T^2 + ...) = 1`. -/
theorem linearFactor_mul_geometricSeries {R : Type*} [Ring R] (c : R) :
    linearFactor c * geometricSeries c = (oneSeries : Series R) := by
  funext n
  change cauchyMul (linearFactor c) (geometricSeries c) n = oneSeries n
  rw [cauchyMul_apply]
  cases n with
  | zero =>
    simp [linearFactor, geometricSeries, oneSeries]
  | succ k =>
    change
      Finset.sum (Finset.range (k + 1 + 1))
          (fun i => linearFactor c i * geometricSeries c (k + 1 - i)) = 0
    rw [Finset.sum_range_succ']
    rw [Finset.sum_range_succ']
    have h_tail :
        Finset.sum (Finset.range k)
            (fun i => linearFactor c (i + 1 + 1) *
              geometricSeries c (k + 1 - (i + 1 + 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [linearFactor]
    rw [h_tail]
    have h_pow : c * c ^ k = c ^ (k + 1) := by
      rw [pow_succ']
    simp [linearFactor, geometricSeries, h_pow]

/-- The quadratic factor `1 - aT + qT^2` as a formal series. -/
def quadraticFactor {R : Type*} [Ring R] (a q : R) : Series R :=
  fun n => if n = 0 then 1 else if n = 1 then -a else if n = 2 then q else 0

@[simp]
theorem quadraticFactor_apply {R : Type*} [Ring R] (a q : R) (n : ℕ) :
    quadraticFactor a q n = if n = 0 then 1 else if n = 1 then -a else if n = 2 then q else 0 :=
  rfl

/-- Finite Cauchy-series factorization: `(1 - αT) * (1 - βT) = 1 - (α+β)T + αβT²`. -/
theorem linearFactor_mul_linearFactor {R : Type*} [CommRing R] (α β : R) :
    linearFactor α * linearFactor β = quadraticFactor (α + β) (α * β) := by
  funext n
  change cauchyMul (linearFactor α) (linearFactor β) n =
    quadraticFactor (α + β) (α * β) n
  rw [cauchyMul_apply]
  rcases n with _ | _ | _ | n
  · simp [linearFactor, quadraticFactor]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp [linearFactor, quadraticFactor]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp [linearFactor, quadraticFactor]
  · have h_zero :
        Finset.sum (Finset.range (n + 3 + 1))
            (fun i => linearFactor α i * linearFactor β (n + 3 - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        have h_ne_zero : n + 3 - 0 ≠ 0 := by omega
        have h_ne_one : n + 3 - 0 ≠ 1 := by omega
        simp [linearFactor]
      · by_cases hi1 : i = 1
        · subst hi1
          have h_ne_zero : n + 3 - 1 ≠ 0 := by omega
          have h_ne_one : n + 3 - 1 ≠ 1 := by omega
          simp [linearFactor]
        · simp [linearFactor, hi0, hi1]
    rw [h_zero]
    simp [quadraticFactor]

/-- The coefficient series assigned to a class by a symmetric-power coefficient function. -/
def Z {R : Type*} (x : R) (S : R → ℕ → R) : Series R :=
  fun n => S x n

/--
If the symmetric-power coefficients satisfy the Cauchy convolution relation
for `y + u`, then the associated zeta series is multiplicative.
-/
theorem mot_zeta_mult {R : Type*} [Semiring R] (y u : R) (S : R → ℕ → R)
    (h :
      ∀ n,
        S (y + u) n =
          Finset.sum (Finset.range (n + 1)) (fun i => S y i * S u (n - i))) :
    Z (y + u) S = Z y S * Z u S := by
  funext n
  change S (y + u) n = cauchyMul (Z y S) (Z u S) n
  rw [cauchyMul_apply]
  exact h n

end InfoGeometry.Canonical.KapranovZetaSeries
