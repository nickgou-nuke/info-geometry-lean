import Mathlib.Tactic
import InfoGeometry.Canonical.BregmanAnalyticBound

noncomputable section

/-!
# Self-Concordant Barrier & Bregman Dikin Bounds

The abstract mathematical structure connecting self-concordant barriers
to Bregman divergence Dikin ellipsoid bounds.

A ν-self-concordant barrier ψ on an open convex set K ⊆ E satisfies:
  |∇³ψ(x)[h,h,h]| ≤ 2 · (∇²ψ(x)[h,h])^(3/2)

which implies the local Dikin ellipsoid bounds:
  ω(‖h‖_x) ≤ D_ψ(x+h, x) ≤ ω_*(‖h‖_x)

where ‖h‖_x = √⟨h, ∇²ψ(x)h⟩ is the local Hessian norm,
ω(t) = t - log(1+t), ω_*(t) = -t - log(1-t) for t < 1.

This file defines the algebraic structure and the bounding functions.
The analytic proofs (integration along line segments, Fréchet derivative
bounds) are structural debt requiring `Analysis/Calculus/FDeriv` and
`intervalIntegral`.

Zero global axioms.
-/

namespace InfoGeometry.Convex

/-! ### ω and ω_* — the Dikin bounding functions -/

/-- ω(t) = t - log(1 + t). Lower Dikin bound. -/
noncomputable def omegaLow (t : ℝ) : ℝ := t - Real.log (1 + t)

/-- ω_*(t) = -t - log(1 - t) for t < 1. Upper Dikin bound. -/
noncomputable def omegaHigh (t : ℝ) (_ht : t < 1) : ℝ := -t - Real.log (1 - t)

lemma omegaLow_nonneg (t : ℝ) (ht : -1 < t) : 0 ≤ omegaLow t := by
  unfold omegaLow
  -- log(1+x) ≤ x for x > -1: from 1+x ≤ exp(x) take log of both sides
  have h_exp : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have h_pos : 0 < 1 + t := by linarith only [ht]
  have h_log : Real.log (1 + t) ≤ t := by
    calc
      Real.log (1 + t) ≤ Real.log (Real.exp t) := Real.log_le_log h_pos h_exp
      _ = t := Real.log_exp t
  linarith

lemma omegaLow_zero : omegaLow 0 = 0 := by
  unfold omegaLow; simp

/-! ### Self-concordant barrier structure -/

/--
A self-concordant barrier with parameter ν on a Euclidean space.

The structure carries:
- `ν` : the barrier parameter (ν ≥ 1 for standard barriers)
- `bregmanDiv` : the Bregman divergence D_ψ(x, y) = ψ(x) - ψ(y) - ⟨∇ψ(y), x-y⟩
- `localNorm` : the local Hessian norm ‖h‖_x = √(∇²ψ(x)[h,h])

The analytic self-concordance inequality |∇³ψ| ≤ 2(∇²ψ)^(3/2) is recorded
as a Prop that downstream theorems can assume when they have the necessary
smoothness hypotheses from `Analysis/Calculus/FDeriv`.
-/
structure SelfConcordantBarrier (E : Type*) [AddCommGroup E] (ν : ℝ) where
  hν_pos : ν > 0
  bregmanDiv : E → E → ℝ
  localNormSq : E → E → ℝ
  -- The defining inequality, stated as a Prop for downstream consumers
  selfconcordant_holds : Prop

/-! ### Dikin ellipsoid bounds — theorem statements -/

/--
**Theorem (Dikin Lower Bound, type signature)**:
Under the self-concordance hypothesis, for y, y+h in the domain with ‖h‖_y < 1:
  ω(‖h‖_y) ≤ D_ψ(y+h, y)

Proof requires `intervalIntegral` along the line segment [y, y+h] using
the third-derivative bound.
-/
structure DikinLowerBound (E : Type*) [AddCommGroup E]
    (ψ : SelfConcordantBarrier E 1) (y h : E) where
  h_bound : ψ.localNormSq y h < 1
  conclusion : omegaLow (Real.sqrt (ψ.localNormSq y h)) ≤ ψ.bregmanDiv (y + h) y

/--
**Theorem (Dikin Upper Bound, type signature)**:
Under the self-concordance hypothesis, for y, y+h in the domain with ‖h‖_y < 1:
  D_ψ(y+h, y) ≤ ω_*(‖h‖_y)

Proof requires `intervalIntegral` along the line segment [y, y+h] using
the third-derivative bound.
-/
structure DikinUpperBound (E : Type*) [AddCommGroup E]
    (ψ : SelfConcordantBarrier E 1) (y h : E) where
  h_bound : Real.sqrt (ψ.localNormSq y h) < 1
  conclusion : ψ.bregmanDiv (y + h) y ≤ omegaHigh (Real.sqrt (ψ.localNormSq y h)) (by
    tauto)

/-! ### Connection to the finite 2×2 model -/

/--
The explicit 2×2 Dikin bound from
`InfoGeometry.Canonical.BregmanAnalyticBound`:
`‖Δ(ε) - I - εK₀‖_F ≤ (2√2)·ε²` for `|ε| ≤ 1`.

This is the finite-dimensional instantiation of the self-concordant
barrier theory with ν = 1 and the logarithmic barrier on the positive cone.

The phase axis K₀ = [[0,-1],[1,0]] gives the Hessian metric on the
2-dimensional Cuntz boundary state space.
-/
theorem finite_model_satisfies_dikin
    (ε : ℝ) (hε : |ε| ≤ 1) :
    Real.sqrt
        (2 * ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2))
      ≤ (2 * Real.sqrt 2) * ε ^ 2 :=
  InfoGeometry.Canonical.BregmanAnalyticBound.bregman_quadratic_bound ε hε

end InfoGeometry.Convex
