import Mathlib
import InfoGeometry.Canonical.QuantumG2FusionCoherenceDatum

open InfoGeometry.Canonical.QuantumG2FusionCoherenceDatum

/-!
# Non-Abelian braid data

This file defines the algebraic condition of two noncommuting braid
generators on a fusion space.  It does not claim existence for a particular
fusion datum.
-/

namespace InfoGeometry.Canonical.QuantumG2NonAbelianBraidData

variable {Sector : Type u} {𝕜 : Type u} [CommRing 𝕜]
variable (D : QuantumG2FusionCoherenceDatum Sector 𝕜)

abbrev ThreeParticleFusionSpace (a c : Sector) :=
  D.leftAssociatedFusionSpace a a a c

/-- Two invertible linear transformations that do not commute. -/
structure NonAbelianBraidData (𝕜 : Type u) (M : Type u)
    [CommRing 𝕜] [AddCommGroup M] [Module 𝕜 M] where
  sigma1 : M ≃ₗ[𝕜] M
  sigma2 : M ≃ₗ[𝕜] M
  non_commuting : sigma1 * sigma2 ≠ sigma2 * sigma1

/-- A fusion sector admits noncommuting braid data in some total channel. -/
def IsNonAbelianAnyon (a : Sector) : Prop :=
  ∃ (c : Sector),
    letI := D.instAddCommGroupLeft a a a c
    letI := D.instModuleLeft a a a c
    Nonempty (NonAbelianBraidData 𝕜 (ThreeParticleFusionSpace D a c))

end InfoGeometry.Canonical.QuantumG2NonAbelianBraidData
