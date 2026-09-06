import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

namespace InfoGeometry.Canonical.CategoricalRiemannRigidity

open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/-- A zero of `f` whose real part lies in the open critical strip. -/
def IsCriticalStripZero (f : ℂ → ℂ) (s : ℂ) : Prop :=
  f s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- Every selected zero lies on the critical line exactly when every selected
zero is fixed by `s ↦ 1 - star s`. -/
theorem criticalStripZeros_on_line_iff_fixed_by_reflection (f : ℂ → ℂ) :
    (∀ s, IsCriticalStripZero f s → s.re = 1 / 2) ↔
      (∀ s, IsCriticalStripZero f s → s = 1 - star s) := by
  constructor
  · intro h s hs
    exact (critical_line_fixed_locus_iff s).2 (h s hs)
  · intro h s hs
    exact (critical_line_fixed_locus_iff s).1 (h s hs)

/-- The usual critical-strip formulation of the Riemann hypothesis. This is a
definition, not a proof of the hypothesis. -/
def RiemannHypothesisCriticalStrip : Prop :=
  ∀ s, IsCriticalStripZero riemannZeta s → s.re = 1 / 2

/-- Reflection-fixed formulation of the same zero-location assertion. This
does not provide a categorical or spectral realization of zeta zeros. -/
def RiemannZeroReflectionRigidity : Prop :=
  ∀ s, IsCriticalStripZero riemannZeta s → s = 1 - star s

theorem riemannHypothesisCriticalStrip_iff_zeroReflectionRigidity :
    RiemannHypothesisCriticalStrip ↔ RiemannZeroReflectionRigidity :=
  criticalStripZeros_on_line_iff_fixed_by_reflection riemannZeta

end InfoGeometry.Canonical.CategoricalRiemannRigidity
