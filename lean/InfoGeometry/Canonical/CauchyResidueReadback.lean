import InfoGeometry.Canonical.RealHomologyCohomologyDictionary
import InfoGeometry.Canonical.DrazinHodgeResidueBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace CauchyResidueReadback

open InfoGeometry.Canonical.RealHomologyCohomologyDictionary
open InfoGeometry.Canonical.DrazinHodgeResidueBridge

/-!
# Cauchy / residue readback

This file records the real Hestenes--Krein readback of Cauchy/residue language.

No complex contour integral, scalar-complex holomorphy, or analytic ODE theorem
is introduced here.  The implemented meanings are:

* Cauchy vanishing: a boundary paired with a boundary-vanishing witness is zero;
* Cauchy homology invariance: such witnesses depend only on homology class;
* residue readout: scalar readout through the calibrated Drazin complementary
  projector, equivalently through the calibrated harmonic projector.
-/

/-! ## Real Cauchy/Stokes vanishing from boundary-vanishing witnesses -/

section BoundaryPairing

variable {Chain Cochain : Type*}
variable [AddCommGroup Chain] [Module ℝ Chain]

variable (B : RealBoundaryOperator Chain)
variable (P : RealPairing Chain Cochain)

/--
Real Cauchy vanishing: a boundary has zero readout against a witness that
vanishes on generated boundaries.
-/
@[rep_depth operator]
theorem cauchy_vanishing_on_boundary
    {c : Chain} {φ : Cochain}
    (hc : B.IsBoundary c)
    (hφ : P.VanishesOnBoundaries B φ) :
    P.pairing c φ = 0 := by
  rcases hc with ⟨b, hb⟩
  rw [← hb]
  exact hφ b

/--
Real Cauchy homology invariance: boundary-vanishing witnesses are constant on
homology-equivalence classes.
-/
@[rep_depth operator]
theorem cauchy_readout_homology_invariant
    {x y : Chain} {φ : Cochain}
    (hxy : B.HomologyEquivalent x y)
    (hφ : P.VanishesOnBoundaries B φ) :
    P.pairing x φ = P.pairing y φ :=
  P.pairing_descends_to_homology_equiv B hxy hφ

/--
If a boundary is homologous to zero, its readout vanishes against every
boundary-vanishing witness.
-/
@[rep_depth operator]
theorem cauchy_vanishing_of_homologous_zero
    {c : Chain} {φ : Cochain}
    (hc : B.HomologyEquivalent c 0)
    (hφ : P.VanishesOnBoundaries B φ) :
    P.pairing c φ = 0 := by
  have h := cauchy_readout_homology_invariant B P hc hφ
  have hzero : P.pairing 0 φ = 0 := by
    simpa using P.sub_left 0 0 φ
  rw [h, hzero]

end BoundaryPairing

/-! ## Scalar residue readouts through the Drazin/Hodge calibration -/

section DrazinResidue

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/--
Real Drazin residue readout: evaluate the scalar witness on the Drazin
generalized-null representative selected by the complementary projector.
-/
@[rep_depth krein]
def drazinResidueReadout
    (R : DrazinHodgeResidueCalibration (E := E))
    (φ : E →L[ℝ] ℝ)
    (x : E) : ℝ :=
  φ (R.CIK.spectralComplementaryProjector x)

/--
Hodge/harmonic residue readout: evaluate the scalar witness on the supplied
harmonic representative.
-/
@[rep_depth krein]
def harmonicResidueReadout
    (R : DrazinHodgeResidueCalibration (E := E))
    (φ : E →L[ℝ] ℝ)
    (x : E) : ℝ :=
  φ (R.HarmonicProjector x)

/--
The harmonic residue readout equals the Drazin residue readout under the
supplied Drazin/Hodge calibration.
-/
@[rep_depth krein]
theorem harmonicResidueReadout_eq_drazinResidueReadout
    (R : DrazinHodgeResidueCalibration (E := E))
    (φ : E →L[ℝ] ℝ)
    (x : E) :
    harmonicResidueReadout R φ x = drazinResidueReadout R φ x := by
  unfold harmonicResidueReadout drazinResidueReadout
  exact R.scalarReadout_harmonicProjector_eq_drazinComplement φ x

/--
On a Drazin-residue representative, the residue readout is the ordinary scalar
readout of that representative.
-/
@[rep_depth krein]
theorem drazinResidueReadout_of_drazinResidue
    (R : DrazinHodgeResidueCalibration (E := E))
    (φ : E →L[ℝ] ℝ)
    {x : E}
    (hx : R.IsDrazinResidue x) :
    drazinResidueReadout R φ x = φ x := by
  unfold drazinResidueReadout
  unfold DrazinHodgeResidueCalibration.IsDrazinResidue at hx
  rw [hx]

/--
On a harmonic representative, the Drazin residue readout is the ordinary scalar
readout, by the calibrated identification of harmonic and Drazin-residue
representatives.
-/
@[rep_depth krein]
theorem drazinResidueReadout_of_harmonicRepresentative
    (R : DrazinHodgeResidueCalibration (E := E))
    (φ : E →L[ℝ] ℝ)
    {x : E}
    (hx : R.IsHarmonicRepresentative x) :
    drazinResidueReadout R φ x = φ x :=
  drazinResidueReadout_of_drazinResidue R φ
    ((R.harmonicRepresentative_iff_drazinResidue x).1 hx)

/--
On a `Delta`-zero representative, the Drazin residue readout is the ordinary
scalar readout, by the supplied Hodge-kernel calibration.
-/
@[rep_depth krein]
theorem drazinResidueReadout_of_deltaZero
    (R : DrazinHodgeResidueCalibration (E := E))
    (φ : E →L[ℝ] ℝ)
    {x : E}
    (hx : R.IsDeltaZero x) :
    drazinResidueReadout R φ x = φ x :=
  drazinResidueReadout_of_drazinResidue R φ
    ((R.drazinResidue_iff_deltaZero x).2 hx)

/--
The Drazin residue readout is unchanged if the input is first projected to the
Drazin complementary sector.
-/
@[rep_depth krein]
theorem drazinResidueReadout_projected
    (R : DrazinHodgeResidueCalibration (E := E))
    (φ : E →L[ℝ] ℝ)
    (x : E) :
    drazinResidueReadout R φ (R.CIK.spectralComplementaryProjector x) =
      drazinResidueReadout R φ x := by
  unfold drazinResidueReadout
  have hIdem := R.CIK.spectralComplementaryProjector_idempotent
  have h := congrArg (fun F : EndH => F x) hIdem
  simpa using congrArg φ h

end DrazinResidue

end CauchyResidueReadback
