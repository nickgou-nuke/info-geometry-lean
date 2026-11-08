import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealHestenesKreinHomology
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical.DrazinHodgeResidueBridge

open InfoGeometry.Canonical

/-!
# Drazin/Hodge residue bridge

This file is the witness-gated bridge between the Drazin generalized-null
sector and a supplied Hodge/harmonic representative sector.

The key calibration is explicit:

`HarmonicProjector = CIK.spectralComplementaryProjector`.

No theorem here claims that an arbitrary Hodge Laplacian has kernel equal to the
Drazin null sector.  The Laplacian readback is carried by the supplied witness
`harmonic_fixed_iff_delta_zero`.
-/

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/--
Calibration identifying a supplied harmonic projector with the Drazin
complementary projector.

`Delta` is the Hodge/Laplacian operator whose kernel is represented by the
harmonic projector through the explicit field `harmonic_fixed_iff_delta_zero`.
-/
@[rep_depth krein]
structure DrazinHodgeResidueCalibration where
  /-- Certified Drazin/Moore--Penrose inverse-kernel owner. -/
  CIK : CertifiedInverseKernel E

  /-- Supplied Hodge/Laplacian operator. -/
  Delta : EndH

  /-- Supplied harmonic projector. -/
  HarmonicProjector : EndH

  /-- The supplied harmonic projector is idempotent. -/
  HarmonicProjector_idempotent :
    HarmonicProjector * HarmonicProjector = HarmonicProjector

  /-- Calibration: the harmonic projector is the Drazin complementary projector. -/
  harmonic_eq_drazinComplement :
    HarmonicProjector = CIK.spectralComplementaryProjector

  /-- Supplied Hodge readback: harmonic fixed points are exactly `Delta`-zero states. -/
  harmonic_fixed_iff_delta_zero :
    ∀ x : E, HarmonicProjector x = x ↔ Delta x = 0

namespace DrazinHodgeResidueCalibration

variable (R : DrazinHodgeResidueCalibration (E := E))

/-- Drazin-null/residue representative predicate selected by `P₀`. -/
@[rep_depth krein]
def IsDrazinResidue (x : E) : Prop :=
  R.CIK.spectralComplementaryProjector x = x

/-- Harmonic representative predicate selected by the calibrated harmonic projector. -/
@[rep_depth krein]
def IsHarmonicRepresentative (x : E) : Prop :=
  R.HarmonicProjector x = x

/-- Laplacian-kernel representative predicate. -/
@[rep_depth krein]
def IsDeltaZero (x : E) : Prop :=
  R.Delta x = 0

/-- The harmonic projector is definitionally read back as the Drazin complement by calibration. -/
@[rep_depth krein]
theorem harmonicProjector_eq_drazinComplement :
    R.HarmonicProjector = R.CIK.spectralComplementaryProjector :=
  R.harmonic_eq_drazinComplement

/-- Harmonic representatives are exactly Drazin-residue representatives. -/
@[rep_depth krein]
theorem harmonicRepresentative_iff_drazinResidue
    (x : E) :
    R.IsHarmonicRepresentative x ↔ R.IsDrazinResidue x := by
  unfold IsHarmonicRepresentative IsDrazinResidue
  rw [R.harmonic_eq_drazinComplement]

/-- Drazin residues are exactly harmonic representatives. -/
@[rep_depth krein]
theorem drazinResidue_iff_harmonicRepresentative
    (x : E) :
    R.IsDrazinResidue x ↔ R.IsHarmonicRepresentative x :=
  (R.harmonicRepresentative_iff_drazinResidue x).symm

/-- Harmonic representatives are exactly `Delta`-zero states by the supplied Hodge witness. -/
@[rep_depth krein]
theorem harmonicRepresentative_iff_deltaZero
    (x : E) :
    R.IsHarmonicRepresentative x ↔ R.IsDeltaZero x := by
  unfold IsHarmonicRepresentative IsDeltaZero
  exact R.harmonic_fixed_iff_delta_zero x

/-- Drazin residues are exactly `Delta`-zero states under the supplied calibration. -/
@[rep_depth krein]
theorem drazinResidue_iff_deltaZero
    (x : E) :
    R.IsDrazinResidue x ↔ R.IsDeltaZero x := by
  exact (R.drazinResidue_iff_harmonicRepresentative x).trans
    (R.harmonicRepresentative_iff_deltaZero x)

/-- The harmonic projector selects harmonic representatives. -/
@[rep_depth krein]
theorem harmonicProjector_selects_harmonicRepresentative
    (x : E) :
    R.IsHarmonicRepresentative (R.HarmonicProjector x) := by
  unfold IsHarmonicRepresentative
  have h := congrArg (fun F : EndH => F x) R.HarmonicProjector_idempotent
  simpa using h

/-- The Drazin complementary projector selects harmonic representatives by calibration. -/
@[rep_depth krein]
theorem drazinComplement_selects_harmonicRepresentative
    (x : E) :
    R.IsHarmonicRepresentative (R.CIK.spectralComplementaryProjector x) := by
  rw [← R.harmonic_eq_drazinComplement]
  exact R.harmonicProjector_selects_harmonicRepresentative x

/-- The harmonic projector selects Drazin-residue representatives by calibration. -/
@[rep_depth krein]
theorem harmonicProjector_selects_drazinResidue
    (x : E) :
    R.IsDrazinResidue (R.HarmonicProjector x) := by
  exact (R.harmonicRepresentative_iff_drazinResidue (R.HarmonicProjector x)).1
    (R.harmonicProjector_selects_harmonicRepresentative x)

/-- The calibrated harmonic projector has the same action as the Drazin complement. -/
@[rep_depth krein]
theorem harmonicProjector_apply_eq_drazinComplement_apply
    (x : E) :
    R.HarmonicProjector x = R.CIK.spectralComplementaryProjector x := by
  rw [R.harmonic_eq_drazinComplement]

/-- Real scalar readouts through the harmonic projector equal readouts through `P₀`. -/
@[rep_depth krein]
theorem scalarReadout_harmonicProjector_eq_drazinComplement
    (φ : E →L[ℝ] ℝ)
    (x : E) :
    φ (R.HarmonicProjector x) = φ (R.CIK.spectralComplementaryProjector x) := by
  rw [R.harmonicProjector_apply_eq_drazinComplement_apply]

/-- Operator readouts through the harmonic projector equal readouts through `P₀`. -/
@[rep_depth krein]
theorem operatorReadout_harmonicProjector_eq_drazinComplement
    (A : EndH)
    (x : E) :
    A (R.HarmonicProjector x) = A (R.CIK.spectralComplementaryProjector x) := by
  rw [R.harmonicProjector_apply_eq_drazinComplement_apply]

/-- Drazin-residue representatives are fixed by the harmonic projector. -/
@[rep_depth krein]
theorem harmonicProjector_fixes_drazinResidue
    {x : E}
    (hx : R.IsDrazinResidue x) :
    R.HarmonicProjector x = x := by
  exact (R.harmonicRepresentative_iff_drazinResidue x).2 hx

/-- Harmonic representatives are fixed by the Drazin complementary projector. -/
@[rep_depth krein]
theorem drazinComplement_fixes_harmonicRepresentative
    {x : E}
    (hx : R.IsHarmonicRepresentative x) :
    R.CIK.spectralComplementaryProjector x = x := by
  exact (R.harmonicRepresentative_iff_drazinResidue x).1 hx

end DrazinHodgeResidueCalibration

end Core

end InfoGeometry.Canonical.DrazinHodgeResidueBridge
