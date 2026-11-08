import InfoGeometry.Canonical.KreinDoubledAtom
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.RelativePotentialScalarBridge

/-!
# InfoGeometry.Canonical.ModularVolumeDeformationBridge

The relative-volume deformation principle stated in the repo's existing count,
projective, and scalar modular language.

This file introduces no new determinant object. It only packages the already
owned count/projective and scalar surfaces as the canonical log-volume and
negative-log-volume deformation lane.
-/

namespace InfoGeometry.Canonical.ModularVolumeDeformationBridge

open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RelativePotentialScalarBridge

section CountProjective

variable {n : Nat} [Nonempty (Fin n)]

/-- Projective count-side relative density is raw density times the global mass ratio. -/
theorem projective_relativeVolumeDeformation_eq_massRatio_mul_raw
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (i : Fin n) :
    InfoGeometry.Canonical.RelativePotentialCore.relativeDensity
        (α := Fin n) (countRay counts hcounts) (countRay ref href) i
      = (countMass ref href / countMass counts hcounts)
          * relativeCountDensity n counts ref i := by
  exact
    relativeDensity_countRay_eq_massRatio_mul_relativeCountDensity
      (n := n) (counts := counts) (ref := ref)
      (hcounts := hcounts) (href := href) (i := i)

/-- Projective log-volume deformation is raw log-density plus the mass-shift mode. -/
theorem projective_logVolumeDeformation_eq_raw_add_massShift
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (i : Fin n) :
    InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity
        (α := Fin n) (countRay counts hcounts) (countRay ref href) i
      = relativeCountLogDensity n counts ref i
        + countMassShift counts ref hcounts href := by
  exact
    relativeLogDensity_countRay_eq_relativeCountLogDensity_add_massShift
      (n := n) (counts := counts) (ref := ref)
      (hcounts := hcounts) (href := href) (i := i)

/-- Projective log-volume deformation is raw log-density minus the log relative-volume change. -/
theorem projective_logVolumeDeformation_eq_raw_sub_log_countRelativeVolumeChange
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (i : Fin n) :
    InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity
        (α := Fin n) (countRay counts hcounts) (countRay ref href) i
      = relativeCountLogDensity n counts ref i
        - Real.log (countRelativeVolumeChange counts ref hcounts href) := by
  exact
    relativeLogDensity_countRay_eq_relativeCountLogDensity_sub_log_countRelativeVolumeChange
      (n := n) (counts := counts) (ref := ref)
      (hcounts := hcounts) (href := href) (i := i)

/-- Projective modular potential is the raw count profile corrected by the scalar relative-volume mode. -/
theorem projective_modularPotential_eq_raw_sub_scalarModularPotential_relativeVolumeChange
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (i : Fin n) :
    InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential
        (α := Fin n) (countRay counts hcounts) (countRay ref href) i
      = relativeCountModularProfile n counts ref i
        - scalarModularPotential
            (countRelativeVolumeChange counts ref hcounts href)
            (by
              exact div_pos (countMass_pos counts hcounts) (countMass_pos ref href)) := by
  exact
    relativeModularPotential_countRay_eq_relativeCountModularProfile_sub_scalarModularPotential_relativeVolumeChange
      (n := n) (counts := counts) (ref := ref)
      (hcounts := hcounts) (href := href) (i := i)

end CountProjective

section Scalar

theorem scalar_modularPotential_is_neg_log
    (r : ℝ) (hr : 0 < r) :
    scalarModularPotential r hr = -Real.log r :=
  scalarModularPotential_eq_neg_log r hr

end Scalar

end InfoGeometry.Canonical.ModularVolumeDeformationBridge
