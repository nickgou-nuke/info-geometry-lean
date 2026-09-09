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

/-- Finite action-density variation packet. -/
structure EffectiveActionPacket where
  dirac : ℂ
  mass : ℂ
  curvature : ℂ
  torsionNorm : ℂ
  κInv : ℂ
  α : ℂ

/-- The finite emergent-gravity action density. -/
def effectiveActionVariation (p : EffectiveActionPacket) : ℂ :=
  p.dirac - p.mass + ((p.κInv / 2) * p.curvature) + ((p.α / 4) * p.torsionNorm)

/-- Zero torsion removes the torsion contribution from the action density. -/
theorem effectiveActionVariation_zero_torsion (p : EffectiveActionPacket) :
    effectiveActionVariation { p with torsionNorm := 0 } =
      p.dirac - p.mass + ((p.κInv / 2) * p.curvature) := by
  simp [effectiveActionVariation]

/-- The torsion part splits additively from the finite action density. -/
theorem effectiveActionVariation_torsion_split (p : EffectiveActionPacket) :
    effectiveActionVariation p =
      (p.dirac - p.mass + ((p.κInv / 2) * p.curvature)) + ((p.α / 4) * p.torsionNorm) := by
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
