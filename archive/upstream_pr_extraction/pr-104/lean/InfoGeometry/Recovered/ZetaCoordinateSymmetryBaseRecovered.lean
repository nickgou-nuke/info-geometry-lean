import InfoGeometry.Arithmetic.ZetaSouriauComplexLift

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

namespace Recovered

/-!
Recovered base definitions for `InfoGeometry.External.Auto.ZetaCoordinateSymmetry`.

The live external-auto file currently uses these four complex-coordinate names,
but they were depleted from that namespace.  These are the exact local
definitions recovered from `sandbox/ZetaCoordinateSymmetry.lean`; using local
definitions rather than cross-namespace aliases is important because the live
proof scripts simplify by unfolding these names directly.

No analytic zeta function or Riemann-property claim is introduced here.
-/

/-- Complex conjugation in zeta spectral coordinates: `s ↦ conj s`. -/
def conjugationReflection (s : ℂ) : ℂ :=
  star s

/-- Functional-equation reflection in zeta spectral coordinates: `s ↦ 1 - s`. -/
def functionalReflection (s : ℂ) : ℂ :=
  1 - s

/-- Antiunitary critical-line mirror: `s ↦ 1 - conj s`. -/
def antiunitaryCriticalReflection (s : ℂ) : ℂ :=
  1 - star s

/-- Critical line predicate `Re(s) = 1/2`. -/
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

end Recovered

end InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
