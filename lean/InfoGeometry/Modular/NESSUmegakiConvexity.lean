/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit
import InfoGeometry.Modular.CommutantInvariantGKSLFlow
import InfoGeometry.Modular.SchrodingerGKSLFlowBridge

/-!
# Umegaki convexity on strictly positive stationary GKSL operators

This module combines the complex-matrix Schrödinger generator with the full
noncommutative Umegaki relative entropy. Convex mixtures of strictly positive
stationary operators remain strictly positive and stationary, are fixed by
the exponential GKSL flow, and satisfy the relative-entropy convexity bound
in the second argument. The entropy inequality is inherited from operator
concavity of the matrix logarithm and imposes no commutation condition.
-/

noncomputable section

namespace InfoGeometry.Modular.NESSUmegakiConvexity

open Matrix
open InfoGeometry.Modular.CommutantInvariantGKSLFlow
open InfoGeometry.Modular.SchrodingerGKSL
open InfoGeometry.Modular.SchrodingerGKSLFlowBridge
open InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit
open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Convexity of the actual matrix Umegaki divergence along two strictly
positive stationary operators of one Schrödinger GKSL generator. Their
mixture is itself stationary and fixed by the full exponential flow. -/
theorem stationary_mixture_umegaki_convex
    {ι : Type*} [Fintype ι]
    (H ρ σ₁ σ₂ : Mat) (V : ι → Mat) (t : ℝ)
    (hρ : IsStrictlyPositive ρ)
    (hσ₁ : IsStrictlyPositive σ₁) (hσ₂ : IsStrictlyPositive σ₂)
    (ht : 0 < t) (ht' : t < 1)
    (hstat₁ : schrodingerLindbladian H V σ₁ = 0)
    (hstat₂ : schrodingerLindbladian H V σ₂ = 0) :
    let σt := t • σ₁ + (1 - t) • σ₂
    IsStrictlyPositive σt ∧
      schrodingerLindbladian H V σt = 0 ∧
      (∀ s : ℝ, gkslFlow H V s σt = σt) ∧
      umegakiRelativeEntropy (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σt ≤
        (t : ℂ) * umegakiRelativeEntropy
          (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ₁ +
          ((1 - t : ℝ) : ℂ) * umegakiRelativeEntropy
            (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ₂ := by
  let σt : Mat := t • σ₁ + (1 - t) • σ₂
  have hσt : IsStrictlyPositive σt := by
    dsimp [σt]
    apply IsStrictlyPositive.add_nonneg
      (IsStrictlyPositive.smul ht hσ₁)
    exact smul_nonneg (by linarith) hσ₂.nonneg
  have hlin₁ : generatorEnd H V σ₁ = 0 := by
    simpa [generatorEnd, generatorCLM_apply] using hstat₁
  have hlin₂ : generatorEnd H V σ₂ = 0 := by
    simpa [generatorEnd, generatorCLM_apply] using hstat₂
  have hlin_t : generatorEnd H V σt = 0 := by
    dsimp [σt]
    rw [map_add, map_smul, map_smul, hlin₁, hlin₂]
    simp
  have hstat_t : schrodingerLindbladian H V σt = 0 := by
    simpa [generatorEnd, generatorCLM_apply] using hlin_t
  have hconvex := umegakiRelativeEntropy_convex_second_argument
    ρ σ₁ σ₂ t hρ hσ₁ hσ₂ ht ht'
  refine ⟨hσt, hstat_t, ?_, ?_⟩
  · intro s
    exact gkslFlow_fixed_of_generator_eq_zero H σt V hstat_t s
  · simpa [σt, umegakiRelativeEntropy] using hconvex

end InfoGeometry.Modular.NESSUmegakiConvexity
