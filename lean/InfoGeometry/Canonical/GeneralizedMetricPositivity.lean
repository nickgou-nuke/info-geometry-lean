/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GeneralizedSolderingBridge

/-!
# Positivity of the full B-field generalized metric

The existing generalized soldering equivalence pulls the generalized metric
back to the direct sum of two copies of the base symmetric form. Consequently,
an arbitrary skew B-field preserves positive definiteness and nonnegativity.
Nondegeneracy already follows from the metric duality equivalence and does not
require positivity.

All statements use the existing algebraic carrier `E × Module.Dual ℝ E`, with
no finite-dimensional assumption. They do not assert integrability, a choice
of dynamics, or an equivalence of physical theories.
-/

noncomputable section

namespace InfoGeometry.Canonical.GeneralizedMetricPositivity

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum
open InfoGeometry.Canonical.GeneralizedSolderingBridge

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The full B-field metric is the sum of two base-metric squares after the
    existing soldering map removes the B-field shift. -/
theorem generalizedMetricForm_self (G : GeneralizedMetricDatum E)
    (X : PhaseSpaceCarrier E) :
    G.generalizedMetricForm X X =
      G.metric.gFlat X.1 X.1 +
        G.metric.gFlat (G.metric.gFlat.symm (X.2 - G.bField.twist X.1))
          (G.metric.gFlat.symm (X.2 - G.bField.twist X.1)) := by
  rcases X with ⟨x, φ⟩
  have h := generalizedSoldering_generalizedMetricForm G
    ((generalizedSoldering G).symm (x, φ))
    ((generalizedSoldering G).symm (x, φ))
  simp only [generalizedSoldering_apply_symm_apply] at h
  simpa only [generalizedSoldering_symm_apply, add_comm] using h

/-- A nonnegative base form gives a nonnegative full B-field metric. -/
theorem generalizedMetricForm_nonneg (G : GeneralizedMetricDatum E)
    (hG : ∀ x, 0 ≤ G.metric.gFlat x x) (X : PhaseSpaceCarrier E) :
    0 ≤ G.generalizedMetricForm X X := by
  rw [generalizedMetricForm_self]
  exact add_nonneg (hG _) (hG _)

/-- A positive definite base form gives a positive definite full B-field metric. -/
theorem generalizedMetricForm_pos (G : GeneralizedMetricDatum E)
    (hG : ∀ x, x ≠ 0 → 0 < G.metric.gFlat x x)
    (X : PhaseSpaceCarrier E) (hX : X ≠ 0) :
    0 < G.generalizedMetricForm X X := by
  have hn (x : E) : 0 ≤ G.metric.gFlat x x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hG x hx).le
  rw [generalizedMetricForm_self]
  by_cases hx : X.1 = 0
  · have hξ : G.metric.gFlat.symm (X.2 - G.bField.twist X.1) ≠ 0 := by
      intro h
      have hφ : X.2 = 0 := by
        have hflat := congrArg G.metric.gFlat h
        simpa [hx] using hflat
      exact hX (Prod.ext hx hφ)
    exact add_pos_of_nonneg_of_pos (hn _) (hG _ hξ)
  · exact add_pos_of_pos_of_nonneg (hG _ hx) (hn _)

/-- The full B-field metric is nondegenerate even when the base metric is
    indefinite: the supplied duality equivalence suffices. -/
theorem generalizedMetricForm_nondegenerate (G : GeneralizedMetricDatum E) :
    G.generalizedMetricForm.Nondegenerate := by
  have hleft (X : PhaseSpaceCarrier E)
      (hX : ∀ Y, G.generalizedMetricForm X Y = 0) : X = 0 := by
    obtain ⟨U, rfl⟩ := (generalizedSoldering G).surjective X
    have h₁ : U.1 = 0 := by
      apply G.metric.gFlat.injective
      apply LinearMap.ext
      intro y
      have h := hX (generalizedSoldering G (y, 0))
      rw [generalizedSoldering_generalizedMetricForm] at h
      simpa [G.metric.symmetric U.1 y] using h
    have h₂ : U.2 = 0 := by
      apply G.metric.gFlat.injective
      apply LinearMap.ext
      intro y
      have h := hX (generalizedSoldering G (0, y))
      rw [generalizedSoldering_generalizedMetricForm] at h
      simpa using h
    have hU : U = 0 := Prod.ext h₁ h₂
    simp [hU]
  constructor
  · exact hleft
  · intro X hX
    apply hleft X
    intro Y
    rw [G.generalizedMetricForm_symm]
    exact hX Y

/-- Nonnegativity of the generalized metric is equivalent to nonnegativity of
    the base form; a B-field cannot repair a negative base direction. -/
theorem generalizedMetricForm_nonneg_iff (G : GeneralizedMetricDatum E) :
    (∀ X : PhaseSpaceCarrier E, 0 ≤ G.generalizedMetricForm X X) ↔
      (∀ x : E, 0 ≤ G.metric.gFlat x x) := by
  constructor
  · intro h x
    have hp := h (generalizedSoldering G (x, 0))
    rw [generalizedSoldering_generalizedMetricForm] at hp
    simpa using hp
  · intro h X
    exact generalizedMetricForm_nonneg G h X

/-- Positive definiteness of the generalized metric is equivalent to positive
    definiteness of the base form, independently of the skew B-field. -/
theorem generalizedMetricForm_pos_iff (G : GeneralizedMetricDatum E) :
    (∀ X : PhaseSpaceCarrier E, X ≠ 0 → 0 < G.generalizedMetricForm X X) ↔
      (∀ x : E, x ≠ 0 → 0 < G.metric.gFlat x x) := by
  constructor
  · intro h x hx
    have hx0 : (x, (0 : E)) ≠ (0 : E × E) := by
      intro hzero
      exact hx (congrArg Prod.fst hzero)
    have hp := h (generalizedSoldering G (x, 0))
      ((generalizedSoldering G).map_ne_zero_iff.mpr hx0)
    rw [generalizedSoldering_generalizedMetricForm] at hp
    simpa using hp
  · intro h X hX
    exact generalizedMetricForm_pos G h X hX

end InfoGeometry.Canonical.GeneralizedMetricPositivity
