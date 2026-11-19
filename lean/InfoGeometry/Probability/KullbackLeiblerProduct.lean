/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from StatLean/Stat-Lean, Copyright 2024 Junwei Lu and StatLean contributors.
Upstream is distributed under the Apache License, Version 2.0:
https://github.com/StatLean/Stat-Lean/blob/e436d8a184421c2a0ed8db0b2688c6cd26a7f5a2/LICENSE

Source: StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean and KLDivergence.lean
at commit e436d8a184421c2a0ed8db0b2688c6cd26a7f5a2.
Modifications: project namespace; use Mathlib's native data-processing inequality;
retain only the generic invariance/product lemmas; generalize finite products to
an arbitrary common measurable space. No StatLean dependency is added.
-/

import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# KL invariance and finite product additivity

These lemmas use the actual Mathlib measure divergence `InformationTheory.klDiv`.
Invertible reparametrization follows from data processing in both directions.
Product additivity follows from the native kernel chain rule. The finite product
theorem is the measure-theoretic input for the Gaussian covariance computation.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace InfoGeometry.Probability

/-- KL divergence is invariant under a measurable map admitting a measurable left inverse.
Both push-forwards are probability measures; equality follows by applying the data-processing
inequality `klDiv_map_le` to `f` and to its inverse `g`. -/
lemma klDiv_map_eq_of_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {g : β → α} (hf : Measurable f) (hg : Measurable g) (hgf : g ∘ f = id)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  have : IsProbabilityMeasure (μ.map f) := (by infer_instance)
  have : IsProbabilityMeasure (ν.map f) := (by infer_instance)
  refine le_antisymm (InformationTheory.klDiv_map_le μ ν hf) ?_
  have h := InformationTheory.klDiv_map_le (μ.map f) (ν.map f) hg
  rwa [Measure.map_map hg hf, Measure.map_map hg hf, hgf, Measure.map_id, Measure.map_id] at h

/-- KL divergence is invariant under push-forward by a measurable equivalence. -/
lemma klDiv_map_measurableEquiv_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν :=
  klDiv_map_eq_of_comp e.measurable e.symm.measurable
    (by funext x; exact e.symm_apply_apply x) μ ν


variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The residual term in the product chain rule: for product measures with a common first
factor `μ₁` (a probability measure), the KL divergence collapses to the second-factor
divergence. Proved by swapping coordinates (`Measure.prod_swap`) so the common factor becomes
the conditional kernel, then applying `klDiv_compProd_left`. -/
private lemma klDiv_prod_const_fst (μ₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) = klDiv μ₂ ν₂ := by
  rw [← klDiv_map_measurableEquiv_eq (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)
    (μ₁.prod μ₂) (μ₁.prod ν₂),
    show ⇑(MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) = Prod.swap from rfl,
    Measure.prod_swap, Measure.prod_swap, ← Measure.compProd_const, ← Measure.compProd_const,
    klDiv_compProd_left]

/-- **Additivity of KL over products** (Wainwright Eq. (15.11a), two-factor case):
`D(ℙ₁⊗ℙ₂ ‖ ℚ₁⊗ℚ₂) = D(ℙ₁ ‖ ℚ₁) + D(ℙ₂ ‖ ℚ₂)`. Follows from the Mathlib chain rule
`klDiv_compProd_eq_add` applied to the product written as a composition–product with a
constant kernel.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.11a). -/
theorem klDiv_prod_eq_add
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  rw [← Measure.compProd_const (μ := μ₁) (ν := μ₂),
    ← Measure.compProd_const (μ := ν₁) (ν := ν₂), klDiv_compProd_eq_add,
    Measure.compProd_const, Measure.compProd_const, klDiv_prod_const_fst]

/-- **Additivity of KL over a finite product** (non-i.i.d. chain rule):
`D(∏ᵢ μᵢ ‖ ∏ᵢ νᵢ) = ∑ᵢ D(μᵢ ‖ νᵢ)`. -/
lemma klDiv_pi_eq_sum {α : Type*} [MeasurableSpace α] :
    ∀ {d : ℕ} (μ ν : Fin d → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)],
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i)
  | 0, μ, ν, _, _ => by
      have hpi : Measure.pi μ = Measure.pi ν := by
        rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp [hpi, klDiv_self]
  | (n + 1), μ, ν, _, _ => by
      have ih := klDiv_pi_eq_sum (fun j => μ (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
      rw [← klDiv_map_measurableEquiv_eq
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0)
          (Measure.pi μ) (Measure.pi ν),
        (measurePreserving_piFinSuccAbove μ 0).map_eq,
        (measurePreserving_piFinSuccAbove ν 0).map_eq,
        klDiv_prod_eq_add, ih, Fin.sum_univ_succAbove (fun i => klDiv (μ i) (ν i)) 0]


end InfoGeometry.Probability
