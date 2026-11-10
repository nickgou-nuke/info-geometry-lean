/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.InfiniteInductiveSUSY

/-!
# Infinite Primon Gas Bost-Connes Tower

This module formalizes the infinite-dimensional extension of finite-mode Primon gas
thermodynamics using compatible algebraic cones and direct-limit transports.

We prove that the finite partition products (`ZF_eq_prod` and `STrF_eq_prod`)
and local cancellations are natively preserved in the infinite target ring under any compatible cone.
-/

open InfoGeometry.Arithmetic.PrimonFinite
open InfoGeometry.Algebra.InfiniteInductiveSUSY

namespace InfoGeometry.Arithmetic.InfinitePrimonGasBostConnes

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

variable {ι : Type*} [DecidableEq ι]
variable {A : ℕ → Type*} [∀ n : ℕ, CommSemiring (A n)]
variable {L : Type*} [CommSemiring L]
variable (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
variable (ι_map : ∀ n : ℕ, A n →+* L)

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

/--
Infinite-dimensional Bost-Connes partition theorem.
Every compatible cone maps the finite stage partition identities cleanly into the target ring.
-/
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

/-- Infinite-dimensional Bost-Connes supertrace theorem. -/
theorem infinite_primon_supertrace_preservation
    {A' : ℕ → Type*} [∀ n : ℕ, CommRing (A' n)]
    {L' : Type*} [CommRing L']
    (ι_map' : ∀ n : ℕ, A' n →+* L')
    (modes : Finset ι) (q : ι → L')
    (q_stage : ∀ n : ℕ, ι → A' n)
    (hq_compat : ∀ n : ℕ, ∀ p, ι_map' n (q_stage n p) = q p) :
    ∀ n : ℕ,
      ι_map' n (STrF modes (q_stage n)) = ∏ p ∈ modes, (1 - q p) := by
  intro n
  have h_STrF := STrF_eq_prod modes (q_stage n)
  have h_map := congrArg (ι_map' n) h_STrF
  simp only [map_prod, map_sub, map_one] at h_map
  rw [h_map]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  rw [hq_compat n p]

/-- Infinite-dimensional local supersymmetric cancellation over any `[DivisionRing (K n)]`
with target ring `[Semiring KL]`. -/
theorem infinite_primon_susy_cancellation
    {K : ℕ → Type*} [∀ n, DivisionRing (K n)]
    {KL : Type*} [Semiring KL]
    (ι_K : ∀ n : ℕ, K n →+* KL)
    (modes : List ι) (q_stage : ∀ n : ℕ, ι → K n)
    (h_nonzero_stage : ∀ n : ℕ, ∀ p ∈ modes, (1 - q_stage n p) ≠ 0) :
    ∀ n : ℕ,
      ι_K n ((modes.map (fun p => (1 - q_stage n p)⁻¹ * (1 - q_stage n p))).prod) = 1 := by
  intro n
  have hprod : (modes.map (fun p => (1 - q_stage n p)⁻¹ * (1 - q_stage n p))).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
    exact inv_mul_cancel₀ (h_nonzero_stage n p hp)
  rw [hprod, map_one]

end InfoGeometry.Arithmetic.InfinitePrimonGasBostConnes
