import Mathlib.Analysis.Complex.Basic

/-!
# Base zeta coordinate symmetries

This file owns the elementary complex-coordinate formulas used by the zeta
coordinate chart.  It deliberately contains only definitions and definitional
rewrite lemmas; analytic zeta-function claims belong in downstream files.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-- Complex conjugation in zeta spectral coordinates: `s ↦ conj s`. -/
def conjugationReflection (s : ℂ) : ℂ :=
  star s

/-- Functional-equation reflection in zeta spectral coordinates: `s ↦ 1 - s`. -/
def functionalReflection (s : ℂ) : ℂ :=
  1 - s

/-- Antiunitary critical-line mirror: `s ↦ 1 - conj s`. -/
def antiunitaryCriticalReflection (s : ℂ) : ℂ :=
  1 - star s

/-- Critical line predicate `Re(s) = 1 / 2`. -/
def CriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

@[simp] theorem conjugationReflection_eq (s : ℂ) :
    conjugationReflection s = star s := by
  rfl

@[simp] theorem functionalReflection_eq (s : ℂ) :
    functionalReflection s = 1 - s := by
  rfl

@[simp] theorem antiunitaryCriticalReflection_eq (s : ℂ) :
    antiunitaryCriticalReflection s = 1 - star s := by
  rfl

@[simp] theorem criticalLine_iff_re_eq_half (s : ℂ) :
    CriticalLine s ↔ s.re = (1 / 2 : ℝ) := by
  rfl

end InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
