import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteScalarLogLaplace

/-!
# Finite Cartan log-Laplace geometry by directional restriction

A finite-dimensional Cartan/exponential family is restricted to every affine
line `β + t • v`.  Each restriction is an instance of the exact scalar
log-Laplace owner.  Consequently:

* the directional derivative of the Massieu potential is the expected charge
  paired with the direction;
* the second directional derivative is the corresponding variance and is
  nonnegative;
* KL/Bregman identities along a Cartan line are inherited without adding a
  second analytic ontology.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace InfoGeometry.Canonical.FiniteCartanLogLaplace

universe u v

variable {Coord : Type v} [Fintype Coord]

/-- Finite Cartan pairing. -/
def pair (β q : Coord → ℝ) : ℝ :=
  ∑ a : Coord, β a * q a

@[simp] theorem pair_add (β γ q : Coord → ℝ) :
    pair (β + γ) q = pair β q + pair γ q := by
  classical
  unfold pair
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp] theorem pair_smul (t : ℝ) (β q : Coord → ℝ) :
    pair (t • β) q = t * pair β q := by
  classical
  unfold pair
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

variable {Mode : Type u} [Fintype Mode]

/-- A finite positive family carrying a finite-dimensional charge vector. -/
structure Family (Mode : Type u) (Coord : Type v)
    [Fintype Mode] [Fintype Coord] where
  weight : Mode → ℝ
  charge : Mode → Coord → ℝ
  weight_pos : ∀ m, 0 < weight m

namespace Family

variable [Nonempty Mode]
variable (F : Family Mode Coord)

/-- Unnormalized Cartan exponential weight. -/
def unnormalized (β : Coord → ℝ) (m : Mode) : ℝ :=
  F.weight m * Real.exp (pair β (F.charge m))

/-- Finite Cartan partition function. -/
def partition (β : Coord → ℝ) : ℝ :=
  ∑ m : Mode, F.unnormalized β m

/-- Finite Cartan Massieu potential. -/
def logPartition (β : Coord → ℝ) : ℝ :=
  Real.log (F.partition β)

/-- Normalized Cartan Gibbs probability. -/
def probability (β : Coord → ℝ) (m : Mode) : ℝ :=
  F.unnormalized β m / F.partition β

/-- Expected charge coordinate. -/
def expectedCharge (β : Coord → ℝ) (a : Coord) : ℝ :=
  ∑ m : Mode, F.probability β m * F.charge m a

@[simp] theorem unnormalized_pos (β : Coord → ℝ) (m : Mode) :
    0 < F.unnormalized β m := by
  exact mul_pos (F.weight_pos m) (Real.exp_pos _)

@[simp] theorem partition_pos (β : Coord → ℝ) :
    0 < F.partition β := by
  classical
  exact Finset.sum_pos
    (fun m _ => F.unnormalized_pos β m)
    Finset.univ_nonempty

@[simp] theorem partition_ne_zero (β : Coord → ℝ) :
    F.partition β ≠ 0 :=
  ne_of_gt (F.partition_pos β)

@[simp] theorem probability_pos (β : Coord → ℝ) (m : Mode) :
    0 < F.probability β m := by
  exact div_pos (F.unnormalized_pos β m) (F.partition_pos β)

@[simp] theorem sum_probability (β : Coord → ℝ) :
    ∑ m : Mode, F.probability β m = 1 := by
  unfold probability
  rw [← Finset.sum_div]
  change F.partition β / F.partition β = 1
  exact div_self (ne_of_gt (F.partition_pos β))

/-- Scalar exponential family obtained by restricting to `β + t • v`. -/
def scalarRestriction
    (β v : Coord → ℝ) :
    FiniteScalarLogLaplace.Family Mode where
  weight := fun m => F.unnormalized β m
  statistic := fun m => pair v (F.charge m)
  weight_pos := F.unnormalized_pos β

/-- The scalar restriction has exactly the Cartan affine-line weights. -/
theorem scalarRestriction_unnormalized
    (β v : Coord → ℝ) (t : ℝ) (m : Mode) :
    (F.scalarRestriction β v).unnormalized t m =
      F.unnormalized (β + t • v) m := by
  unfold scalarRestriction FiniteScalarLogLaplace.Family.unnormalized unnormalized
  rw [pair_add, pair_smul, Real.exp_add]
  ring

/-- Partition readout along a Cartan affine line. -/
theorem scalarRestriction_partition
    (β v : Coord → ℝ) (t : ℝ) :
    (F.scalarRestriction β v).partition t =
      F.partition (β + t • v) := by
  classical
  unfold FiniteScalarLogLaplace.Family.partition partition
  apply Finset.sum_congr rfl
  intro m hm
  exact F.scalarRestriction_unnormalized β v t m

/-- Log-partition readout along a Cartan affine line. -/
theorem scalarRestriction_logPartition
    (β v : Coord → ℝ) (t : ℝ) :
    (F.scalarRestriction β v).logPartition t =
      F.logPartition (β + t • v) := by
  unfold FiniteScalarLogLaplace.Family.logPartition logPartition
  rw [F.scalarRestriction_partition]

/-- Probability readout along a Cartan affine line. -/
theorem scalarRestriction_probability
    (β v : Coord → ℝ) (t : ℝ) (m : Mode) :
    (F.scalarRestriction β v).probability t m =
      F.probability (β + t • v) m := by
  unfold FiniteScalarLogLaplace.Family.probability probability
  rw [F.scalarRestriction_unnormalized, F.scalarRestriction_partition]

/-- The scalar mean is the expected directional Cartan charge. -/
theorem scalarRestriction_mean
    (β v : Coord → ℝ) (t : ℝ) :
    (F.scalarRestriction β v).mean t =
      ∑ m : Mode,
        F.probability (β + t • v) m * pair v (F.charge m) := by
  rw [(F.scalarRestriction β v).mean_eq_expectation]
  apply Finset.sum_congr rfl
  intro m hm
  rw [F.scalarRestriction_probability]
  rfl

/-- Pairing with the expected charge equals expectation of the paired charge. -/
theorem pair_expectedCharge
    (β v : Coord → ℝ) :
    pair v (F.expectedCharge β) =
      ∑ m : Mode, F.probability β m * pair v (F.charge m) := by
  classical
  unfold pair expectedCharge
  calc
    (∑ a : Coord, v a * ∑ m : Mode, F.probability β m * F.charge m a) =
        ∑ a : Coord, ∑ m : Mode,
          v a * (F.probability β m * F.charge m a) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
    _ = ∑ m : Mode, ∑ a : Coord,
          v a * (F.probability β m * F.charge m a) := by
            rw [Finset.sum_comm]
    _ = ∑ m : Mode,
          F.probability β m *
            (∑ a : Coord, v a * F.charge m a) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            ring

/-- Directional derivative of the Cartan Massieu potential. -/
theorem hasDerivAt_cartanLine_logPartition
    (β v : Coord → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s => F.logPartition (β + s • v))
      (pair v (F.expectedCharge (β + t • v)))
      t := by
  have h := (F.scalarRestriction β v).hasDerivAt_logPartition t
  have hfun :
      (F.scalarRestriction β v).logPartition =
        (fun s => F.logPartition (β + s • v)) := by
    funext s
    exact F.scalarRestriction_logPartition β v s
  rw [hfun] at h
  have hmean := F.scalarRestriction_mean β v t
  have hpair := F.pair_expectedCharge (β + t • v) v
  rw [hmean, ← hpair] at h
  exact h

/-- At the base point, the directional derivative is the mean charge pairing. -/
theorem hasDerivAt_cartanLine_logPartition_zero
    (β v : Coord → ℝ) :
    HasDerivAt
      (fun s : ℝ => F.logPartition (β + s • v))
      (pair v (F.expectedCharge β))
      (0 : ℝ) := by
  have h := F.hasDerivAt_cartanLine_logPartition β v (0 : ℝ)
  simpa [zero_smul] using h

/-- The second directional derivative is the scalar-restriction variance. -/
theorem hasDerivAt_cartanLine_firstDerivative
    (β v : Coord → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s => deriv (fun r => F.logPartition (β + r • v)) s)
      ((F.scalarRestriction β v).variance t)
      t := by
  have h := (F.scalarRestriction β v).hasDerivAt_deriv_logPartition t
  have hbase :
      (F.scalarRestriction β v).logPartition =
        (fun r => F.logPartition (β + r • v)) := by
    funext r
    exact F.scalarRestriction_logPartition β v r
  have hfun : (fun s => deriv (F.scalarRestriction β v).logPartition s) =
      (fun s => deriv (fun r => F.logPartition (β + r • v)) s) := by
    funext s
    rw [hbase]
  rw [hfun] at h
  exact h

/-- KL/Bregman identity on every Cartan affine-line restriction. -/
theorem cartanLine_kl_eq_bregman_reverse
    (β v : Coord → ℝ) (t s : ℝ) :
    (F.scalarRestriction β v).kl t s =
      (F.scalarRestriction β v).bregman s t :=
  (F.scalarRestriction β v).kl_eq_bregman_reverse t s

/-- Every Cartan directional Hessian is nonnegative. -/
theorem cartanLine_secondDerivative_nonnegative
    (β v : Coord → ℝ) (t : ℝ) :
    0 ≤ deriv
      (fun s => deriv (fun r => F.logPartition (β + r • v)) s) t := by
  have h := F.hasDerivAt_cartanLine_firstDerivative β v t
  rw [h.deriv]
  exact (F.scalarRestriction β v).variance_nonnegative t

end Family

end InfoGeometry.Canonical.FiniteCartanLogLaplace

end noncomputable section
