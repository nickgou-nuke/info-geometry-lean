/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.MobiusDual

/-!
# Projective duality and Fenchel--Legendre potentials

The projective line/point pairing is the native dual pairing for the finite
Möbius action.  This file records the exact bridge to Fenchel geometry:
potential-level objectives and gaps are built from that pairing, and the
contragredient action preserves them when the primal and dual potentials are
invariant.  No affine chart or projective quotient is silently identified with
a vector-space model.
-/

namespace InfoGeometry.Projective.ProjectiveFenchelLegendreBridge

open InfoGeometry.Projective.MobiusDual

/-- Fenchel objective on a projective point and its dual projective line. -/
def projectiveFenchelObjective
    (ψ : ProjectivePoint ℝ → ℝ)
    (η : ProjectiveLine ℝ)
    (θ : ProjectivePoint ℝ) : ℝ :=
  pairing η θ - ψ θ

/-- Fenchel gap for a pair of primal and dual projective potentials. -/
def projectiveFenchelGap
    (ψ : ProjectivePoint ℝ → ℝ)
    (ψStar : ProjectiveLine ℝ → ℝ)
    (η : ProjectiveLine ℝ)
    (θ : ProjectivePoint ℝ) : ℝ :=
  ψ θ + ψStar η - pairing η θ

/-- Projective Fenchel majorization, stated against the native line/point pairing. -/
def IsProjectiveFenchelMajorized
    (ψ : ProjectivePoint ℝ → ℝ)
    (ψStar : ProjectiveLine ℝ → ℝ) : Prop :=
  ∀ η θ, projectiveFenchelObjective ψ η θ ≤ ψStar η

theorem projectiveFenchelGap_nonneg
    {ψ : ProjectivePoint ℝ → ℝ}
    {ψStar : ProjectiveLine ℝ → ℝ}
    (hMajorized : IsProjectiveFenchelMajorized ψ ψStar)
    (η : ProjectiveLine ℝ)
    (θ : ProjectivePoint ℝ) :
    0 ≤ projectiveFenchelGap ψ ψStar η θ := by
  unfold projectiveFenchelGap
  have h := hMajorized η θ
  unfold IsProjectiveFenchelMajorized projectiveFenchelObjective at h
  linarith

/-- The projective Fenchel objective is invariant under a contragredient Möbius pair. -/
theorem projectiveFenchelObjective_invariant
    (A : SL2 ℝ)
    (ψ : ProjectivePoint ℝ → ℝ)
    (η : ProjectiveLine ℝ)
    (θ : ProjectivePoint ℝ)
    (hψ : ∀ θ, ψ (actPoint A θ) = ψ θ) :
    projectiveFenchelObjective ψ (actLine A η) (actPoint A θ) =
      projectiveFenchelObjective ψ η θ := by
  unfold projectiveFenchelObjective
  rw [hψ θ, contragredient_pairing_invariant]

/-- The projective Fenchel gap is invariant when both potentials respect the action. -/
theorem projectiveFenchelGap_invariant
    (A : SL2 ℝ)
    (ψ : ProjectivePoint ℝ → ℝ)
    (ψStar : ProjectiveLine ℝ → ℝ)
    (η : ProjectiveLine ℝ)
    (θ : ProjectivePoint ℝ)
    (hψ : ∀ θ, ψ (actPoint A θ) = ψ θ)
    (hψStar : ∀ η, ψStar (actLine A η) = ψStar η) :
    projectiveFenchelGap ψ ψStar (actLine A η) (actPoint A θ) =
      projectiveFenchelGap ψ ψStar η θ := by
  unfold projectiveFenchelGap
  rw [hψ θ, hψStar η, contragredient_pairing_invariant]

/-- Majorization transports along an invariant contragredient Möbius action. -/
theorem projectiveFenchelMajorized_act
    (A : SL2 ℝ)
    {ψ : ProjectivePoint ℝ → ℝ}
    {ψStar : ProjectiveLine ℝ → ℝ}
    (hMajorized : IsProjectiveFenchelMajorized ψ ψStar)
    (hψ : ∀ θ, ψ (actPoint A θ) = ψ θ)
    (hψStar : ∀ η, ψStar (actLine A η) = ψStar η)
    (η : ProjectiveLine ℝ)
    (θ : ProjectivePoint ℝ) :
    projectiveFenchelObjective ψ (actLine A η) (actPoint A θ) ≤
      ψStar (actLine A η) := by
  rw [projectiveFenchelObjective_invariant A ψ η θ hψ]
  rw [hψStar η]
  exact hMajorized η θ

end InfoGeometry.Projective.ProjectiveFenchelLegendreBridge
