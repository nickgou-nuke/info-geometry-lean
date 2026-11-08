/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RelativeEntropyFlow

namespace InfoGeometry.Quantum.RelativeEntropyFlow

open Matrix InfoGeometry.Dynamics.KanDecomposition InfoGeometryCore

/-- Exact trace correction, valid for every matrix, without positivity assumptions. -/
theorem quantumShearSandwich_trace (ρ : M2C) (δ : ℂ) :
    Matrix.trace (quantumShearSandwich ρ δ) = Matrix.trace ρ +
      (δ * ρ 1 0 + star δ * ρ 0 1 + (Complex.normSq δ : ℂ) * ρ 1 1) := by
  rw [← Complex.mul_conj δ]
  simp only [quantumShearSandwich, componentN_eq, Matrix.trace_fin_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  simp
  ring

/-- A nonzero shear can preserve individual input traces exactly on this equation. -/
theorem quantumShearSandwich_trace_eq_iff (ρ : M2C) (δ : ℂ) :
    Matrix.trace (quantumShearSandwich ρ δ) = Matrix.trace ρ ↔
      δ * ρ 1 0 + star δ * ρ 0 1 + (Complex.normSq δ : ℂ) * ρ 1 1 = 0 := by
  rw [quantumShearSandwich_trace, add_eq_left]

theorem quantumShearSandwich_maximallyMixed_trace (δ : ℂ) :
    Matrix.trace (quantumShearSandwich maximallyMixedState δ) =
      1 + (Complex.normSq δ : ℂ) / 2 := by
  rw [quantumShearSandwich_trace, maximallyMixedState_trace]
  simp [maximallyMixedState, div_eq_mul_inv]

/-- The maximally mixed state detects every nonzero shear's trace defect. -/
theorem quantumShearSandwich_maximallyMixed_trace_iff (δ : ℂ) :
    Matrix.trace (quantumShearSandwich maximallyMixedState δ) = 1 ↔ δ = 0 := by
  rw [quantumShearSandwich_maximallyMixed_trace]
  constructor
  · intro he
    have hr := congrArg Complex.re he
    have hn : Complex.normSq δ = 0 := by
      simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re,
        Complex.ofReal_re] at hr
      linarith
    exact Complex.normSq_eq_zero.mp hn
  · rintro rfl
    simp

/-- Universal trace preservation holds precisely at the identity shear. -/
theorem quantumShearSandwich_trace_preserving_iff (δ : ℂ) :
    (∀ ρ : M2C, Matrix.trace (quantumShearSandwich ρ δ) = Matrix.trace ρ) ↔ δ = 0 := by
  constructor
  · intro ht
    apply (quantumShearSandwich_maximallyMixed_trace_iff δ).mp
    simpa only [maximallyMixedState_trace] using ht maximallyMixedState
  · rintro rfl
    intro ρ
    simp [quantumShearSandwich]

end InfoGeometry.Quantum.RelativeEntropyFlow
