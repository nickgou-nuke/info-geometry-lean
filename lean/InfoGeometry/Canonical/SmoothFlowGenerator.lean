/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FlowConjugation
import InfoGeometry.Canonical.SmoothDiffeomorphismPushforward

/-!
# Differentiating conjugation of a smooth spatial flow

A homomorphism from real additive time is only algebraic data. The theorems
below explicitly require its trajectories to have the displayed derivative
at zero. The chain rule then intertwines conjugation of the flow with the
derivative pushforward of its generator. No ODE existence or uniqueness is
assumed. Only the implication from flow symmetry to generator symmetry is
asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.SmoothFlowGenerator

open SmoothDiffeomorphismPushforward
open scoped FlowConjugation SmoothDiffeomorphismPushforward ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative at zero of a conjugated trajectory is the actual Fréchet
pushforward of the original generator. -/
theorem hasDerivAt_conjugateFlow
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E)
    (X : E → E)
    (hX : ∀ x, HasDerivAt (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0)
    (g : smoothDiffeomorphismSubgroup E) (y : E) :
    HasDerivAt (fun t : ℝ => ((g • Φ) (Multiplicative.ofAdd t)).val y)
      (pushforward g X y) 0 := by
  have hzero : (Φ (Multiplicative.ofAdd (0 : ℝ))).val (g.val.symm y) =
      g.val.symm y := by
    change (Φ 1).val (g.val.symm y) = g.val.symm y
    rw [map_one]
    rfl
  have hg := (g.property.1.differentiable (by simp) (g.val.symm y)).hasFDerivAt
  have h := hg.comp_hasDerivAt_of_eq 0 (hX (g.val.symm y)) hzero.symm
  exact h

/-- A symmetry of the full flow fixes its generator. The converse would
require an integral-curve uniqueness theorem and is not used here. -/
theorem flowSymmetry_le_vectorFieldSymmetry
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E)
    (X : E → E)
    (hX : ∀ x, HasDerivAt (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0) :
    MulAction.stabilizer (smoothDiffeomorphismSubgroup E) Φ ≤
      vectorFieldSymmetrySubgroup X := by
  intro g hg
  apply (mem_vectorFieldSymmetrySubgroup_iff g X).mpr
  intro y
  have h := hasDerivAt_conjugateFlow Φ X hX g y
  have hfix : g • Φ = Φ := hg
  rw [hfix] at h
  exact h.unique (hX y)

/-- A commutative-time flow preserves its own differentiable generator. -/
theorem flow_pushforward_generator
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E)
    (X : E → E)
    (hX : ∀ x, HasDerivAt (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0)
    (t : Multiplicative ℝ) :
    pushforward (Φ t) X = X :=
  flowSymmetry_le_vectorFieldSymmetry Φ X hX
    (FlowConjugation.flow_value_mem_stabilizer Φ t)

end InfoGeometry.Canonical.SmoothFlowGenerator
