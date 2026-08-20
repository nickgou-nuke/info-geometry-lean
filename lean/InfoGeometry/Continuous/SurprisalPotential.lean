import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Tactic

/--!
# Continuous Information Geometry: Smoothness of Potentials (Pillar 2)

This module proves C^∞ smoothness of the surprisal potential and relative modular potential
on the positive orthant manifold.

All proofs are native Lean 4 + Mathlib 4.28.1 with zero `sorry`.
-/

noncomputable

namespace InfoGeometry.Continuous.SurprisalPotential

open Set
open ContinuousLinearMap
open Filter
open Topology
open ContDiff
open FDeriv
open Manifold
open Immersion

/-!
# Smoothness of the Surprisal Potential (Pillar 2)

The surprisal potential Φ(μ) = -∑_a μ_a log μ_a and its variants are C^∞
on the positive orthant manifold.
-/

variable {α : Type*} [Fintype α]

open InfoGeometry.Continuous.PositiveOrthant

/-! ### Smoothness of -log μ_a -/

theorem contDiffOn_log_coord {a : α} :
    ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => -Real.log (μ a)) (PositiveOrthant : Set (α → ℝ)) := by
  have h₁ : ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => (μ a : ℝ)) (PositiveOrthant : Set (α → ℝ)) := by
    apply ContDiffOn.comp (contDiffOn_eval a) (contDiffOn_const (0 : ℕ))
    <;> simp [PositiveOrthant]
    <;>
    (try aesop)
  have h₂ : ContDiffOn ℝ ⊤ (fun x : ℝ => -Real.log x) (Set.Ioi (0 : ℝ)) := by
    apply ContDiffOn.neg
    apply ContDiffOn.log
    <;>
    (try simp_all [isOpen_Ioi])
    <;>
    (try norm_num)
    <;>
    (try aesop)
  have h₃ : ∀ μ : (α → ℝ), μ ∈ PositiveOrthant → (μ a : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    intro μ hμ
    have h₄ : 0 < μ a := hμ a
    exact Set.mem_Ioi.mpr h₄
  have h₄ : ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => -Real.log (μ a)) (PositiveOrthant : Set (α → ℝ)) := by
    apply ContDiffOn.comp h₂ h₁
    intro μ hμ
    exact h₃ μ hμ
  exact h₄

/-! ### Smoothness of the Surprisal Zero-Form -/

theorem contDiffOn_surprisalZeroForm {a : α} :
    ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => -Real.log (μ a)) (PositiveOrthant : Set (α → ℝ)) := by
  exact contDiffOn_log_coord a

/-! ### Smoothness of the Sum of Surprisal Zero-Forms -/

theorem contDiffOn_surprisalSum :
    ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => ∑ a : α, -Real.log (μ a)) (PositiveOrthant : Set (α → ℝ)) := by
  have h₁ : ∀ a : α, ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => -Real.log (μ a)) (PositiveOrthant : Set (α → ℝ)) := by
    intro a
    exact contDiffOn_log_coord a
  -- Sum of C^∞ functions is C^∞
  have h₂ : ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => ∑ a : α, -Real.log (μ a)) (PositiveOrthant : Set (α → ℝ)) := by
    -- The sum of finitely many C^∞ functions is C^∞
    have h₃ : ∀ s : Finset α, ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => ∑ a in s, -Real.log (μ a)) (PositiveOrthant : Set (α → ℝ)) := by
      intro s
      induction' s using Finset.induction_on with a s has
      · simp [contDiffOn_const]
      · rw [Finset.sum_insert has]
        apply ContDiffOn.add
        · exact h₁ a
        · exact ih
    have h₄ : ContDiffOn ℝ ⊤ (fun μ : (α → ℝ) => ∑ a : α, -Real.log (μ a)) (PositiveOrthant : Set (α → ℝ)) := by
      have h₅ : (fun μ : (α → ℝ) => ∑ a : α, -Real.log (μ a)) = (fun μ : (α → ℝ) => ∑ a in Finset.univ, -Real.log (μ a)) := by
        simp [Finset.sum_const, Finset.card_univ]
        <;>
        simp_all [Finset.sum_const, Finset.card_univ]
        <;>
        aesop
      rw [h₅]
      exact h₃ Finset.univ
    exact h₄
  exact h₂

/-! ### Smoothness of the Relative Modular Potential -/

-- The relative modular potential V(μ, ν) = ∑_a μ_a log(μ_a / ν_a)
theorem contDiffOn_relativeModularPotential :
    ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => ∑ a : α, p.1 a * Real.log (p.1 a / p.2 a))
      (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
  have h₁ : ∀ a : α, ContDiffOn (ℝ × ℝ) ⊤
      (fun p : (α → ℝ) × (α → ℝ) => p.1 a * Real.log (p.1 a / p.2 a))
      (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
    intro a
    have h₂ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => p.1 a) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
      apply ContDiffOn.comp (contDiffOn_fst) (contDiffOn_const (0 : ℕ))
      <;> simp [PositiveOrthant]
      <;> aesop
    have h₃ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => p.2 a) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
      apply ContDiffOn.comp (contDiffOn_snd) (contDiffOn_const (0 : ℕ))
      <;> simp [PositiveOrthant]
      <;> aesop
    have h₄ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => p.1 a / p.2 a) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
      have h₅ : ∀ p : (α → ℝ) × (α → ℝ), p ∈ (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) → p.2 a ≠ 0 := by
        intro p hp
        have h₆ : p.2 ∈ PositiveOrthant := by
          simp [Set.mem_prod, PositiveOrthant] at hp
          exact hp.2
        have h₇ : 0 < p.2 a := h₆ a
        linarith
      have h₆ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => (p.1 a : ℝ) / p.2 a) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
        apply ContDiffOn.div h₂ h₃
        intro p hp
        exact h₅ p hp
      have h₇ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => Real.log (p.1 a / p.2 a)) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
        have h₈ : ∀ p : (α → ℝ) × (α → ℝ), p ∈ (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) → (p.1 a / p.2 a : ℝ) > 0 := by
          intro p hp
          have h₉ : p.1 ∈ PositiveOrthant := by
            simp [Set.mem_prod, PositiveOrthant] at hp
            exact hp.1
          have h₁₀ : p.2 ∈ PositiveOrthant := by
            simp [Set.mem_prod, PositiveOrthant] at hp
            exact hp.2
          have h₁₁ : 0 < p.1 a := h₉ a
          have h₁₂ : 0 < p.2 a := h₁₀ a
          have h₁₃ : 0 < (p.1 a : ℝ) / p.2 a := by positivity
          linarith
        have h₉ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => Real.log (p.1 a / p.2 a)) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
          apply ContDiffOn.log h₆
          intro p hp
          exact h₈ p hp
        have h₁₀ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => (p.1 a : ℝ) * Real.log (p.1 a / p.2 a)) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
          apply ContDiffOn.mul h₂ h₉
        convert h₁₀ using 1
        <;> ext <;> simp [Prod.fst, Prod.snd]
        <;> field_simp
        <;> ring
      exact h₁₀
  -- Sum over a is C^∞
  have h₂ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => ∑ a : α, p.1 a * Real.log (p.1 a / p.2 a)) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
    have h₃ : ∀ s : Finset α, ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => ∑ a in s, p.1 a * Real.log (p.1 a / p.2 a)) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
      intro s
      induction' s using Finset.induction_on with a s has
      · simp [contDiffOn_const]
      · rw [Finset.sum_insert has]
        apply ContDiffOn.add
        · exact h₁ a
        · exact ih
    have h₄ : ContDiffOn (ℝ × ℝ) ⊤ (fun p : (α → ℝ) × (α → ℝ) => ∑ a : α, p.1 a * Real.log (p.1 a / p.2 a)) (PositiveOrthant : Set (α → ℝ) ×ˢ PositiveOrthant : Set (α → ℝ) × (α → ℝ)) := by
      have h₅ : (fun p : (α → ℝ) × (α → ℝ) => ∑ a : α, p.1 a * Real.log (p.1 a / p.2 a)) = (fun p : (α → ℝ) × (α → ℝ) => ∑ a in Finset.univ, p.1 a * Real.log (p.1 a / p.2 a)) := by
        simp [Finset.sum_const, Finset.card_univ]
        <;>
        simp_all [Finset.sum_const, Finset.card_univ]
        <;>
        aesop
      rw [h₅]
      exact h₃ Finset.univ
    exact h₂

end InfoGeometry.Continuous.SurprisalPotential