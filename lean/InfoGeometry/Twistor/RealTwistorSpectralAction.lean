/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A real constrained spectral action and its actual derivative

The action is defined from a genuine bilinear form and a linear operator.
Its scalar directional derivative is computed using Mathlib calculus, even
when the algebraic state carrier has no topology. Independent state and
multiplier variations derive both the eigen-equation and unit normalization.
This is a stationary Rayleigh--Ritz action, not a time-path action.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealSpectralAction

/-- Scalar arithmetic used only after the bilinear/operator expressions are evaluated. -/
private theorem scalar_action_line (hxx hvx hvv nxx nvx nvv E μ t : ℝ) :
    (hxx + t * hvx + t * (hvx + t * hvv)) / 2 -
        (E + t * μ) * (nxx + t * nvx + t * (nvx + t * nvv) - 1) / 2 =
      hxx / 2 - E * (nxx - 1) / 2 +
        t * (hvx - E * nvx - μ * (nxx - 1) / 2) +
        t ^ 2 * (hvv / 2 - E * nvv / 2 - μ * nvx) -
        t ^ 3 * (μ * nvv / 2) := by
  ring

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The multiplier enforces positive unit normalization at stationary points. -/
def action (B : LinearMap.BilinForm ℝ V) (H : Module.End ℝ V)
    (x : V) (E : ℝ) : ℝ :=
  B x (H x) / 2 - E * (B x x - 1) / 2

/-- The linear term, subsequently proved to be the actual directional derivative. -/
def firstVariation (B : LinearMap.BilinForm ℝ V) (H : Module.End ℝ V)
    (x : V) (E : ℝ) (v : V) (μ : ℝ) : ℝ :=
  B v (H x - E • x) - μ * (B x x - 1) / 2

/-- Exact finite expansion; no limit or omitted higher-order term is used. -/
theorem action_line (B : LinearMap.BilinForm ℝ V) (H : Module.End ℝ V)
    (hB : ∀ x y, B x y = B y x)
    (hH : ∀ x y, B (H x) y = B x (H y))
    (x v : V) (E μ t : ℝ) :
    action B H (x + t • v) (E + t * μ) =
      action B H x E + t * firstVariation B H x E v μ +
        t ^ 2 * (B v (H v) / 2 - E * B v v / 2 - μ * B v x) -
        t ^ 3 * (μ * B v v / 2) := by
  simp only [action, firstVariation, map_add, map_smul, map_sub,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hB x v, ← hH x v, hB (H x) v]
  exact scalar_action_line (B x (H x)) (B v (H x)) (B v (H v))
    (B x x) (B v x) (B v v) E μ t

/-- Directional differentiability includes variation of the multiplier. -/
theorem hasDerivAt_action_line
    (B : LinearMap.BilinForm ℝ V) (H : Module.End ℝ V)
    (hB : ∀ x y, B x y = B y x)
    (hH : ∀ x y, B (H x) y = B x (H y))
    (x v : V) (E μ : ℝ) :
    HasDerivAt (fun t : ℝ => action B H (x + t • v) (E + t * μ))
      (firstVariation B H x E v μ) 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) (action B H x E)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (firstVariation B H x E v μ))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
        (B v (H v) / 2 - E * B v v / 2 - μ * B v x))).sub
      (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (μ * B v v / 2))
  convert h using 1
  · funext t
    exact action_line B H hB hH x v E μ t
  · simp

theorem deriv_action_line
    (B : LinearMap.BilinForm ℝ V) (H : Module.End ℝ V)
    (hB : ∀ x y, B x y = B y x)
    (hH : ∀ x y, B (H x) y = B x (H y))
    (x v : V) (E μ : ℝ) :
    deriv (fun t : ℝ => action B H (x + t • v) (E + t * μ)) 0 =
      firstVariation B H x E v μ :=
  (hasDerivAt_action_line B H hB hH x v E μ).deriv

/-- Stationarity is stated in terms of the actual scalar derivative. -/
def Stationary (B : LinearMap.BilinForm ℝ V) (H : Module.End ℝ V)
    (x : V) (E : ℝ) : Prop :=
  ∀ (v : V) (μ : ℝ),
    deriv (fun t : ℝ => action B H (x + t • v) (E + t * μ)) 0 = 0

/-- The normalized eigen-equation is a conclusion, not input data. -/
theorem stationary_iff
    (B : LinearMap.BilinForm ℝ V) (H : Module.End ℝ V)
    (hB : ∀ x y, B x y = B y x)
    (hH : ∀ x y, B (H x) y = B x (H y))
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    (x : V) (E : ℝ) :
    Stationary B H x E ↔ H x = E • x ∧ B x x = 1 := by
  simp only [Stationary, deriv_action_line B H hB hH]
  constructor
  · intro h
    have hn := h 0 1
    simp only [firstVariation, map_zero, LinearMap.zero_apply, one_mul,
      zero_sub] at hn
    have hnorm : B x x = 1 := by linarith
    have hr := h (H x - E • x) 0
    simp only [firstVariation, zero_mul, zero_div, sub_zero] at hr
    have hz : H x - E • x = 0 := by
      by_contra hne
      exact (ne_of_gt (hpos _ hne)) hr
    exact ⟨sub_eq_zero.mp hz, hnorm⟩
  · rintro ⟨he, hn⟩ v μ
    simp [firstVariation, he, hn]

/-- Unit normalization prevents the zero-state loophole. -/
theorem normalized_ne_zero (B : LinearMap.BilinForm ℝ V) (x : V)
    (hx : B x x = 1) : x ≠ 0 := by
  intro h
  subst x
  simp at hx

end InfoGeometry.Twistor.RealSpectralAction
