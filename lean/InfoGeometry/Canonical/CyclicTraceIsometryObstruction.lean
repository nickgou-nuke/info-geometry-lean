import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace InfoGeometry.Canonical.CyclicTraceIsometryObstruction

open scoped BigOperators

/-!
An abstract form of the finite Cuntz/CCR trace obstruction.  The carrier is
an arbitrary associative ring; no matrix coordinates, diagonalization, or
commutativity of the carrier is used.
-/

variable {A C : Type*} [Ring A] [Ring C] [Nontrivial C]

/-- Two one-sided inverses whose range idempotents partition the unit force
every cyclic additive trace to vanish on the unit. -/
theorem cyclic_additive_trace_vanishes_on_unit
    (x₀ y₀ x₁ y₁ : A) (τ : A →+ C)
    (hcyc : ∀ a b : A, τ (a * b) = τ (b * a))
    (h₀ : y₀ * x₀ = 1) (h₁ : y₁ * x₁ = 1)
    (hsum : x₀ * y₀ + x₁ * y₁ = 1) :
    τ 1 = 0 := by
  have ht₀ : τ (x₀ * y₀) = τ 1 := by
    rw [hcyc, h₀]
  have ht₁ : τ (x₁ * y₁) = τ 1 := by
    rw [hcyc, h₁]
  have hτsum := congrArg τ hsum
  rw [map_add, ht₀, ht₁] at hτsum
  have h : τ 1 + τ 1 = τ 1 + 0 := by simpa using hτsum
  exact add_left_cancel h

/-- For any finite partition by one-sided range products, a cyclic additive
readout of the unit is fixed by multiplication by the number of branches.
This is the exact conclusion over arbitrary rings; further vanishing requires
the target additive group to have no torsion at the corresponding integer. -/
theorem cyclic_trace_finite_partition_fixed_point
    {ι : Type*} [Fintype ι]
    (x y : ι → A) (τ : A →+ C)
    (hcyc : ∀ a b : A, τ (a * b) = τ (b * a))
    (hleft : ∀ i, y i * x i = 1)
    (hsum : ∑ i : ι, x i * y i = 1) :
    ((Finset.univ : Finset ι).card : ℕ) • τ 1 = τ 1 := by
  have hterm (i : ι) : τ (x i * y i) = τ 1 := by
    rw [hcyc, hleft i]
  have hτsum : (∑ i : ι, τ (x i * y i)) = τ 1 := by
    simpa only [map_sum] using congrArg τ hsum
  calc
    ((Finset.univ : Finset ι).card : ℕ) • τ 1 = ∑ i : ι, τ 1 := by simp
    _ = ∑ i : ι, τ (x i * y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hterm i).symm
    _ = τ 1 := hτsum

/-- Consequently, a normalized cyclic additive trace cannot exist for such a
two-range partition in a nontrivial target ring. -/
theorem no_normalized_cyclic_additive_trace
    (x₀ y₀ x₁ y₁ : A) (τ : A →+ C)
    (hcyc : ∀ a b : A, τ (a * b) = τ (b * a))
    (h₀ : y₀ * x₀ = 1) (h₁ : y₁ * x₁ = 1)
    (hsum : x₀ * y₀ + x₁ * y₁ = 1)
    (hnorm : τ 1 = 1) : False := by
  have hzero := cyclic_additive_trace_vanishes_on_unit x₀ y₀ x₁ y₁ τ hcyc h₀ h₁ hsum
  exact zero_ne_one (hzero.symm.trans hnorm)

/-- A proper one-sided isometry cannot satisfy the CAR relation in a
nontrivial ring: the two equations force its range idempotent to vanish and
then force the unit to vanish. -/
theorem no_car_isometry_in_nontrivial_ring
    [Nontrivial A] (x xstar : A)
    (hiso : xstar * x = 1)
    (hcar : xstar * x + x * xstar = 1) : False := by
  have hrange : x * xstar = 0 := by
    rw [hiso] at hcar
    have h : (1 : A) + x * xstar = 1 + 0 := by simpa using hcar
    exact add_left_cancel h
  have hone : (1 : A) = 0 := by
    calc
      (1 : A) = (xstar * x) * (xstar * x) := by rw [hiso]; simp
      _ = xstar * (x * xstar) * x := by simp only [mul_assoc]
      _ = 0 := by rw [hrange, mul_zero, zero_mul]
  exact one_ne_zero hone

end InfoGeometry.Canonical.CyclicTraceIsometryObstruction
