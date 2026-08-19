import InfoGeometry.Canonical.EmergentGravity
import InfoGeometry.Canonical.StressEnergyTensor

noncomputable section

namespace InfoGeometry.Canonical.EmergentGravity

open Complex

/-
Finite action-variation bridge for the emergent-gravity lane.

This file stays at the algebraic shadow level owned by the repo:

* the effective action density is split into Dirac, mass, curvature, and
  torsion-norm slots;
* the torsion contribution is isolated as an explicit additive variation;
* the Belinfante-Rosenfeld tensor is re-exported as a symmetric finite readout
  through the existing stress-energy owner file.

It does not derive the field equations from a continuum variational calculus.
-/

/-- The finite emergent-gravity action density. -/
def effectiveActionVariation
    (dirac mass curvature torsionNorm κInv α : ℂ) : ℂ :=
  dirac - mass + ((κInv / 2) * curvature) + ((α / 4) * torsionNorm)

/-- Zero torsion removes the torsion contribution from the action density. -/
theorem effectiveActionVariation_zero_torsion
    (dirac mass curvature κInv α : ℂ) :
    effectiveActionVariation dirac mass curvature 0 κInv α =
      dirac - mass + ((κInv / 2) * curvature) := by
  simp [effectiveActionVariation]

/-- The torsion part splits additively from the finite action density. -/
theorem effectiveActionVariation_torsion_split
    (dirac mass curvature torsionNorm κInv α : ℂ) :
    effectiveActionVariation dirac mass curvature torsionNorm κInv α =
      (dirac - mass + ((κInv / 2) * curvature)) + ((α / 4) * torsionNorm) := by
  simp [effectiveActionVariation]

/-- A finite Belinfante readout packaged from the owner tensor. -/
def belinfanteReadout {M : Type*} [AddCommGroup M] [Module ℂ M]
    (tensor : SpinorBilinearTensor M) (mu nu : ℕ) : M :=
  stress_energy_tensor tensor mu nu

/-- The finite Belinfante readout is symmetric in the two indices. -/
theorem belinfanteReadout_symmetric {M : Type*} [AddCommGroup M] [Module ℂ M]
    (tensor : SpinorBilinearTensor M) (mu nu : ℕ) :
    belinfanteReadout tensor mu nu = belinfanteReadout tensor nu mu := by
  simpa [belinfanteReadout] using stress_energy_symmetry tensor mu nu

end InfoGeometry.Canonical.EmergentGravity
