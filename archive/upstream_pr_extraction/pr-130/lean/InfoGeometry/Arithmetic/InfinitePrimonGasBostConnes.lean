/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Algebra.InfiniteInductiveSUSY

/-!
# Compatible-cone transport of finite prime products

This module transports finite product identities through compatible ring maps.
It does not construct an infinite-dimensional partition function, a direct
limit, or an analytic Bost--Connes system.
-/

set_option linter.unusedSectionVars false

open InfoGeometry.Arithmetic.PrimonFinite
open InfoGeometry.Algebra.InfiniteInductiveSUSY

namespace InfoGeometry.Arithmetic.InfinitePrimonGasBostConnes

variable {ι : Type*} [DecidableEq ι]
variable {A : ℕ → Type*} [∀ n : ℕ, CommRing (A n)]
variable {L : Type*} [CommRing L]
variable (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
variable (ι_map : ∀ n : ℕ, A n →+* L)
variable (hcone : CompatibleCone φ ι_map)

/-- Stepwise transport of the partition function over expanding finite modes. -/
theorem primon_partition_step
    (modes : ℕ → Finset ι) (q : ∀ k, ι → A k)
    (h_modes : ∀ n : ℕ, modes (Nat.succ n) = modes n)
    (h_q : ∀ n : ℕ, ∀ p, φ n (q n p) = q (Nat.succ n) p)
    (n : ℕ) :
    φ n (ZF (modes n) (q n)) = ZF (modes (Nat.succ n)) (q (Nat.succ n)) := by
  classical
  dsimp [ZF, weight]
  rw [h_modes n]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro S _hS
  rw [map_prod]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact h_q n p

/-- A compatible cone transports the finite partition product identity. -/
theorem infinite_primon_partition_preservation
    (modes : Finset ι) (q : ι → L)
    (q_stage : ∀ n : ℕ, ι → A n)
    (hq_compat : ∀ n : ℕ, ∀ p, ι_map n (q_stage n p) = q p) :
    ∀ n : ℕ,
      ι_map n (ZF modes (q_stage n)) = ∏ p ∈ modes, (1 + q p) := by
  intro n
  have h_ZF := ZF_eq_prod modes (q_stage n)
  have h_map := congrArg (ι_map n) h_ZF
  simp only [map_prod, map_add, map_one] at h_map
  rw [h_map]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  rw [hq_compat n p]

/-- A compatible cone transports the finite signed product identity. -/
theorem infinite_primon_supertrace_preservation
    (modes : Finset ι) (q : ι → L)
    (q_stage : ∀ n : ℕ, ι → A n)
    (hq_compat : ∀ n : ℕ, ∀ p, ι_map n (q_stage n p) = q p) :
    ∀ n : ℕ,
      ι_map n (STrF modes (q_stage n)) = ∏ p ∈ modes, (1 - q p) := by
  intro n
  have h_STrF := STrF_eq_prod modes (q_stage n)
  have h_map := congrArg (ι_map n) h_STrF
  simp only [map_prod, map_sub, map_one] at h_map
  rw [h_map]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  rw [hq_compat n p]

/-- Local cancellation after transport through a field-valued cone. -/
theorem infinite_primon_susy_cancellation
    {K : ℕ → Type*} [∀ n, Field (K n)]
    {KL : Type*} [Field KL]
    (ι_K : ∀ n : ℕ, K n →+* KL)
    (modes : Finset ι) (q_stage : ∀ n : ℕ, ι → K n)
    (h_nonzero_stage : ∀ n : ℕ, ∀ p ∈ modes, (1 - q_stage n p) ≠ 0) :
    ∀ n : ℕ,
      ι_K n (∏ p ∈ modes, ((1 - q_stage n p)⁻¹ * (1 - q_stage n p))) = 1 := by
  intro n
  have h_local := local_susy_cancellation (K := K n) modes (q_stage n) (h_nonzero_stage n)
  rw [h_local, map_one]

end InfoGeometry.Arithmetic.InfinitePrimonGasBostConnes
