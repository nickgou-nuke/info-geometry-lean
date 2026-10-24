/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceReflectionContracts
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Reflection parity, weighted traces, and real CAR normalization

The two-parameter combination is not asserted to be a condensate or a
self-adjoint Hamiltonian. A weighted algebra element is not automatically
a normalized positive state, nor is its chiral trace a baryon number.
-/

namespace InfoGeometry.Core.PeirceParityWeights

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.PeirceReflectionContracts
open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Singular.MoorePenrose

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {d b : A}

/-- Preserve the source's actual algebraic combination without its physical label. -/
def oddCombination (α β : R) (d b : A) : A :=
  α • transitionVelocity d b + β • wheelGenerator d b

/-- Arbitrary diagonal weights on the two active supports. -/
def diagonalWeight (x y : R) (d b : A) : A :=
  x • polePlus d b + y • poleMinus d b

/-- Both components are odd under the grading, independently of their coefficients. -/
theorem combination_anticommutes (h : IsDualSeedPair d b) (α β : R) :
    phasePolarization d b * oddCombination α β d b +
      oddCombination α β d b * phasePolarization d b = 0 := by
  have hj : phasePolarization d b * wheelGenerator d b +
      wheelGenerator d b * phasePolarization d b = 0 := by
    change (polePlus d b - poleMinus d b) * (d - b) +
      (d - b) * (polePlus d b - poleMinus d b) = 0
    simp only [sub_mul, mul_sub, h.pd, h.pb, h.qd, h.qb,
      h.dp, h.bp, h.dq, h.bq]
    abel
  calc
    _ = α • (phasePolarization d b * transitionVelocity d b +
        transitionVelocity d b * phasePolarization d b) +
      β • (phasePolarization d b * wheelGenerator d b +
        wheelGenerator d b * phasePolarization d b) := by
        simp only [oddCombination, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
        module
    _ = 0 := by rw [h.polarization_velocity, hj, smul_zero, smul_zero, add_zero]

/-- Exact parity action, not an identification of this action with physical CP. -/
theorem combination_reflection (h : IsDualSeedPair d b) (α β : R) :
    transitionVelocity d b * oddCombination α β d b * transitionVelocity d b =
      oddCombination α (-β) d b := by
  simp only [oddCombination, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    (reflection_generator_parities h).1, (reflection_generator_parities h).2,
    smul_neg, neg_smul]

/-- Fixed and negative-fixed defects need no cancellation of two. -/
theorem combination_defects (h : IsDualSeedPair d b) (α β : R) :
    transitionVelocity d b * oddCombination α β d b * transitionVelocity d b -
      oddCombination α β d b = -((2 * β) • wheelGenerator d b) ∧
    transitionVelocity d b * oddCombination α β d b * transitionVelocity d b +
      oddCombination α β d b = (2 * α) • transitionVelocity d b := by
  rw [combination_reflection h]
  unfold oddCombination
  constructor <;> module

/-- Exact fixed-point criterion includes torsion and degenerate seeds. -/
theorem combination_fixed_iff (h : IsDualSeedPair d b) (α β : R) :
    transitionVelocity d b * oddCombination α β d b * transitionVelocity d b =
      oddCombination α β d b ↔ (2 * β) • wheelGenerator d b = 0 := by
  rw [← sub_eq_zero, (combination_defects h α β).1, neg_eq_zero]

/-- The negative-fixed criterion has an independent even-component defect. -/
theorem combination_negfixed_iff (h : IsDualSeedPair d b) (α β : R) :
    transitionVelocity d b * oddCombination α β d b * transitionVelocity d b =
      -oddCombination α β d b ↔ (2 * α) • transitionVelocity d b = 0 := by
  rw [eq_neg_iff_add_eq_zero, (combination_defects h α β).2]

/-- The chiral observable reads the signed difference of diagonal weights. -/
theorem grading_weight (h : IsDualSeedPair d b) (x y : R) :
    phasePolarization d b * diagonalWeight x y d b =
      x • polePlus d b - y • poleMinus d b := by
  change (polePlus d b - poleMinus d b) *
    (x • polePlus d b + y • poleMinus d b) = _
  simp only [mul_add, sub_mul, mul_smul_comm, h.pp, h.pq, h.qp, h.qq,
    sub_zero, zero_sub, smul_neg, sub_eq_add_neg]

/-- Traciality derives equal support traces; it is not a separate supplied equality. -/
theorem trace_weights (h : IsDualSeedPair d b)
    (τ : A →ₗ[R] R) (hτ : ∀ x y, τ (x * y) = τ (y * x)) (x y : R) :
    τ (diagonalWeight x y d b) = (x + y) * τ (polePlus d b) ∧
    τ (phasePolarization d b * diagonalWeight x y d b) =
      (x - y) * τ (polePlus d b) := by
  have he : τ (poleMinus d b) = τ (polePlus d b) := hτ b d
  constructor
  · simp only [diagonalWeight, map_add, map_smul, smul_eq_mul, he]
    ring
  · rw [grading_weight h]
    simp only [map_sub, map_smul, smul_eq_mul, he]
    ring

/-- A hyperbolic weight convention does not supply unit trace. -/
theorem hyperbolic_trace {A : Type*} [Ring A] [Algebra ℝ A] {d b : A}
    (h : IsDualSeedPair d b) (τ : A →ₗ[ℝ] ℝ)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hn : τ (polePlus d b) = 1)
    (u v : ℝ) (huv : u * u - v * v = 1) :
    τ (diagonalWeight (u * u) (v * v) d b) = 1 + 2 * v * v := by
  rw [(trace_weights h τ hτ _ _).1, hn, mul_one]
  linarith

/-- No odd expectation in a reflection-invariant element under an actual real trace. -/
theorem invariant_weight_trace_zero {A : Type*} [Ring A] [Algebra ℝ A] {d b ρ : A}
    (h : IsDualSeedPair d b) (τ : A →ₗ[ℝ] ℝ)
    (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hρ : transitionVelocity d b * ρ * transitionVelocity d b = ρ) :
    τ (phasePolarization d b * ρ) = 0 := by
  have ht : τ (phasePolarization d b * ρ) = -τ (phasePolarization d b * ρ) := by
    calc
      _ = τ (phasePolarization d b *
          (transitionVelocity d b * ρ * transitionVelocity d b)) := by rw [hρ]
      _ = τ ((phasePolarization d b * transitionVelocity d b * ρ) *
          transitionVelocity d b) := by simp only [mul_assoc]
      _ = τ (transitionVelocity d b *
          (phasePolarization d b * transitionVelocity d b * ρ)) := hτ _ _
      _ = τ ((transitionVelocity d b * phasePolarization d b *
          transitionVelocity d b) * ρ) := by simp only [mul_assoc]
      _ = -τ (phasePolarization d b * ρ) := by
        rw [(reflection_exchange h).2.2, neg_mul, map_neg]
  linarith

/-- Real/central coefficient CAR mixing uses a sum of squares.
The four inputs can be two distinct particle/hole modes. -/
theorem car_mix_anticommutator (a a' c c' : A)
    (ha : a * a' + a' * a = 1) (hc : c * c' + c' * c = 1)
    (hac : a * c' + c' * a + c * a' + a' * c = 0) (u v : R) :
    (u • a + v • c) * (u • a' + v • c') +
      (u • a' + v • c') * (u • a + v • c) = (u * u + v * v) • (1 : A) := by
  calc
    _ = (u * u) • (a * a' + a' * a) +
      (v * v) • (c * c' + c' * c) +
      (u * v) • (a * c' + c' * a + c * a' + a' * c) := by
        simp only [add_mul, mul_add, smul_mul_smul]
        module
    _ = _ := by rw [ha, hc, hac, smul_zero, add_zero, add_smul]

/-- A sum-one condition preserves this anticommutator. Other CAR equations remain separate. -/
theorem car_mix_normalized (a a' c c' : A)
    (ha : a * a' + a' * a = 1) (hc : c * c' + c' * c = 1)
    (hac : a * c' + c' * a + a' * c + c * a' = 0)
    (u v : R) (huv : u * u + v * v = 1) :
    (u • a + v • c) * (u • a' + v • c') +
      (u • a' + v • c') * (u • a + v • c) = 1 := by
  have hac' : a * c' + c' * a + c * a' + a' * c = 0 := by
    calc _ = a * c' + c' * a + a' * c + c * a' := by abel
         _ = 0 := hac
  rw [car_mix_anticommutator a a' c c' ha hc hac', huv, one_smul]

/-- Mixing a single annihilator with its own partner also has a square obstruction. -/
theorem one_pair_mix_square (h : IsDualSeedPair d b) (u v : R) :
    (u • d + v • b) * (u • d + v • b) = (u * v) • carrierSupport d b := by
  change _ = (u * v) • (d * b + b * d)
  simp only [add_mul, mul_add, smul_mul_smul, h.d_sq, h.b_sq, smul_zero]
  module

end InfoGeometry.Core.PeirceParityWeights
