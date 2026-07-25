import InfoGeometry.Canonical.CategoricalRiemannRigidity
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/-!
# Compatibility Shim for CategoricalRiemannRigidity

Redirects legacy symbols to the canonical owner in `InfoGeometry.Canonical.CategoricalRiemannRigidity`.
-/

open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge
open InfoGeometry.Canonical.CategoricalRiemannRigidity

def antiunitaryCriticalReflection (s : ℂ) : ℂ :=
  1 - star s

theorem antiunitary_fixed_locus_is_critical_line (s : ℂ) :
    antiunitaryCriticalReflection s = s ↔ s.re = 1 / 2 :=
  critical_line_fixed_locus_iff s

def is_colimit_kernel_object (s : ℂ) (riemannZeta : ℂ → ℂ) : Prop :=
  IsCriticalStripZero riemannZeta s

theorem riemann_hypothesis_colimit_rigidity (riemannZeta : ℂ → ℂ) :
    (∀ s, is_colimit_kernel_object s riemannZeta → s.re = 1 / 2) ↔
      (∀ s, is_colimit_kernel_object s riemannZeta → antiunitaryCriticalReflection s = s) := by
  simpa [antiunitaryCriticalReflection, is_colimit_kernel_object] using
    criticalStripZeros_on_line_iff_fixed_by_reflection riemannZeta
