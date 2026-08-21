import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Finite scalar Radon--Nikodym and modular-surprisal shadow

This owner formalizes the finite commutative scalar model. It does not claim
the general Tomita--Takesaki or Connes theory.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConnesAraki

structure FaithfulScalarState where
  density : ℝ
  density_pos : 0 < density

def modularSurprisal (φ : FaithfulScalarState) : ℝ := -Real.log φ.density

def relativeSurprisal (ψ φ : FaithfulScalarState) : ℝ :=
  modularSurprisal ψ - modularSurprisal φ

def cocycle (ψ φ : FaithfulScalarState) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (relativeSurprisal ψ φ : ℂ))

@[simp] theorem cocycle_zero (ψ φ : FaithfulScalarState) :
    cocycle ψ φ 0 = 1 := by
  simp [cocycle]

theorem cocycle_add (ψ φ : FaithfulScalarState) (s t : ℝ) :
    cocycle ψ φ (s + t) = cocycle ψ φ s * cocycle ψ φ t := by
  simp only [cocycle, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem relativeSurprisal_eq_neg_log_density_ratio
    (ψ φ : FaithfulScalarState) :
    relativeSurprisal ψ φ =
      -Real.log (ψ.density / φ.density) := by
  unfold relativeSurprisal modularSurprisal
  rw [Real.log_div (ne_of_gt ψ.density_pos) (ne_of_gt φ.density_pos)]
  ring

end InfoGeometry.Canonical.ConnesAraki

end noncomputable section
