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
