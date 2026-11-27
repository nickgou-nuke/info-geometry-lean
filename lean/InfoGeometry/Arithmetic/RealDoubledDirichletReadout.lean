/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubledSpace
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Actual Dirichlet L-values on the real doubled carrier

The arithmetic boundary is Mathlib's actual `DirichletCharacter.LFunction`.
The target consists of real continuous linear operators on the existing
`DoubledSpace E`, with phase axis `clockAxis = Jε`.

This file constructs the value readout and proves that it detects zeros
faithfully whenever the real seed `E` is nontrivial. It does not assume or
prove GRH. The optional GRH integration applies an externally checked
arithmetic theorem to this concrete readout.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RealDoubledDirichletReadout

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real two-coordinate value acts through the existing `Jε` phase axis. -/
def scalarOp (a b : ℝ) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  a • (1 : DoubledSpace E →L[ℝ] DoubledSpace E) + b • clockAxis

theorem scalarOp_apply (a b : ℝ) (x y : E) :
    scalarOp (E := E) a b (to_doubled x y) =
      to_doubled (a • x - b • y) (a • y + b • x) := by
  apply DoubledSpace.ext <;>
    simp [scalarOp, sub_eq_add_neg]

/-- The scalar readout cannot collapse a nonzero value on a nontrivial seed. -/
theorem scalarOp_eq_zero_iff [Nontrivial E] (a b : ℝ) :
    scalarOp (E := E) a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hfst := congrArg
      (fun A : DoubledSpace E →L[ℝ] DoubledSpace E =>
        WithLp.fst (A (to_doubled x 0))) h
    have hsnd := congrArg
      (fun A : DoubledSpace E →L[ℝ] DoubledSpace E =>
        WithLp.snd (A (to_doubled x 0))) h
    have ha : a • x = 0 := by simpa [scalarOp_apply] using hfst
    have hb : b • x = 0 := by simpa [scalarOp_apply] using hsnd
    exact ⟨(smul_eq_zero.mp ha).resolve_right hx,
      (smul_eq_zero.mp hb).resolve_right hx⟩
  · rintro ⟨rfl, rfl⟩
    apply ContinuousLinearMap.ext
    intro u
    simp [scalarOp]

/-- Real modular reflection reverses precisely the phase coordinate. -/
theorem modular_j_conjugates_scalarOp (a b : ℝ) :
    modular_j * scalarOp (E := E) a b * modular_j = scalarOp a (-b) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [scalarOp, clockAxis, complex_i, modular_j, spectral_epsilon,
      add_comm]

/-- Evaluate Mathlib's actual Dirichlet L-function at the real coordinates
`(sigma, height)` and retain both components as a real operator. -/
def dirichletReadout {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (sigma height : ℝ) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  scalarOp (χ.LFunction ⟨sigma, height⟩).re
    (χ.LFunction ⟨sigma, height⟩).im

theorem dirichletReadout_eq_zero_iff [Nontrivial E]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (sigma height : ℝ) :
    dirichletReadout (E := E) χ sigma height = 0 ↔
      χ.LFunction ⟨sigma, height⟩ = 0 := by
  rw [dirichletReadout, scalarOp_eq_zero_iff]
  exact ⟨fun h => Complex.ext h.1 h.2,
    fun h => by simp [h]⟩

theorem dirichletReadout_ne_zero_iff [Nontrivial E]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (sigma height : ℝ) :
    dirichletReadout (E := E) χ sigma height ≠ 0 ↔
      χ.LFunction ⟨sigma, height⟩ ≠ 0 :=
  not_congr (dirichletReadout_eq_zero_iff χ sigma height)

/-- The zeta specialization uses the actual Mathlib zeta function. -/
def zetaReadout (sigma height : ℝ) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  scalarOp (riemannZeta ⟨sigma, height⟩).re
    (riemannZeta ⟨sigma, height⟩).im

theorem zetaReadout_eq_zero_iff [Nontrivial E] (sigma height : ℝ) :
    zetaReadout (E := E) sigma height = 0 ↔
      riemannZeta ⟨sigma, height⟩ = 0 := by
  rw [zetaReadout, scalarOp_eq_zero_iff]
  exact ⟨fun h => Complex.ext h.1 h.2,
    fun h => by simp [h]⟩

end InfoGeometry.Arithmetic.RealDoubledDirichletReadout
