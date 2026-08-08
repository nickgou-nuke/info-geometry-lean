import InfoGeometry.Thermo.ModularKLDivergence
import InfoGeometry.MeasureProjective
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge
import InfoGeometry.Canonical.DPDWedgeCompatibility
import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ModularKLDivergenceBridge

Repo-native bridge surface for the modular/KL lane on the strict-positive
projective owners.

This file adds no new ontology. It only re-exports and lightly repackages:
- strict-positive generalized-KL scale/shape decomposition;
- projective logarithmic-generator compatibility with relative modular
  potential on `PositiveRay`;
- the equivalent negative-relative-log-density form.
-/

namespace InfoGeometry.Canonical.ModularKLDivergenceBridge

open scoped ENNReal NNReal
open MeasureTheory
open InfoGeometry.PositiveMeasure
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.MeasureProjective
open InfoGeometry.MeasureProjective.ProjectiveState
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativePotentialDiscreteBridge
open InfoGeometry.Canonical.DPDWedgeCompatibility
open InfoGeometry.Canonical.ModularSpectralWedge
open InfoGeometry.Canonical.RelativeModularScaleShapeSplit

section ScaleShape

variable {α : Type*} [Fintype α]

/--
Strict-positive scale/shape split of generalized KL on rays:
projective (shape) term plus radial mass-gauge term.
-/
@[rep_depth projective]
theorem generalizedKL_scale_shape_split
    [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
    Z (α := α) (R := ℝ) μ
      * generalizedKL (α := α)
          (normalize (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) ν)
      + gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  simpa using
    InfoGeometry.Thermo.ModularKLDivergence.generalizedKL_scale_shape_split
      (α := α) μ ν

/-- Equivalent slack split: generalized KL = shape log-ratio part + radial mass slack. -/
@[rep_depth projective]
theorem generalizedKL_eq_klLike_add_massSlack
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
    klLike (α := α) μ ν +
      (Z (α := α) (R := ℝ) ν - Z (α := α) (R := ℝ) μ) := by
  exact generalizedKL_eq_klLike_add_Z (α := α) μ ν

/--
In the strict-positive cone, both scale/shape components in the generalized-KL
split are nonnegative.
-/
@[rep_depth projective]
theorem generalizedKL_scale_shape_terms_nonneg
    [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    0 ≤
        Z (α := α) (R := ℝ) μ
          * generalizedKL (α := α)
              (normalize (α := α) (R := ℝ) μ)
              (normalize (α := α) (R := ℝ) ν)
      ∧
    0 ≤ gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  constructor
  · exact mul_nonneg
      (le_of_lt (PositiveMeasure.Z_pos (α := α) (R := ℝ) μ))
      (PositiveMeasure.generalizedKL_nonneg
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν))
  · exact PositiveMeasure.gklTerm_nonneg
      (Z (α := α) (R := ℝ) μ)
      (Z (α := α) (R := ℝ) ν)
      (PositiveMeasure.Z_pos (α := α) (R := ℝ) μ)
      (PositiveMeasure.Z_pos (α := α) (R := ℝ) ν)

/--
Strict-positive mass mismatch gives strictly positive radial gauge term in the
scale/shape split.
-/
@[rep_depth projective]
theorem generalizedKL_scale_shape_mass_term_pos_of_mass_ne
    [Nonempty α]
    (μ ν : PositiveMeasure α ℝ)
    (hMass : Z (α := α) (R := ℝ) μ ≠ Z (α := α) (R := ℝ) ν) :
    0 < gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  exact PositiveMeasure.gklTerm_pos_of_ne
      (Z (α := α) (R := ℝ) μ)
      (Z (α := α) (R := ℝ) ν)
      (PositiveMeasure.Z_pos (α := α) (R := ℝ) μ)
      (PositiveMeasure.Z_pos (α := α) (R := ℝ) ν)
      hMass

/--
Combined closure package: scale/shape decomposition plus nonnegativity of both
components.
-/
@[rep_depth projective]
theorem generalizedKL_scale_shape_split_with_nonneg
    [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
        Z (α := α) (R := ℝ) μ
          * generalizedKL (α := α)
              (normalize (α := α) (R := ℝ) μ)
              (normalize (α := α) (R := ℝ) ν)
        + gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν)
      ∧
    0 ≤
        Z (α := α) (R := ℝ) μ
          * generalizedKL (α := α)
              (normalize (α := α) (R := ℝ) μ)
              (normalize (α := α) (R := ℝ) ν)
      ∧
    0 ≤ gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  refine ⟨generalizedKL_scale_shape_split (α := α) μ ν, ?_⟩
  exact generalizedKL_scale_shape_terms_nonneg (α := α) μ ν

end ScaleShape

section DrazinModularScaleShape

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {α : Type*} [Fintype α] [Nonempty α]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Projective (shape) part of generalized KL on the strict-positive cone. -/
@[rep_depth projective]
noncomputable def generalizedKL_activeShapeTerm
    (μ ν : PositiveMeasure α ℝ) : ℝ :=
  Z (α := α) (R := ℝ) μ
    * generalizedKL (α := α)
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν)

/-- Radial/gauge (mass) part of generalized KL on the strict-positive cone. -/
@[rep_depth projective]
noncomputable def generalizedKL_kernelMassTerm
    (μ ν : PositiveMeasure α ℝ) : ℝ :=
  gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν)

/--
Capstone bridge: strict-positive generalized-KL scale/shape split together with
explicit Drazin/wedge projector alignment.

This theorem adds no new ontology; it packages:
- KL shape/scale decomposition,
- kernel identification `P_0 = P_D^⊥` on the compatible lane,
- active-sector identification `active = 1 - P_0`.
-/
@[rep_depth transport, capstone]
theorem relativeModularScaleShapeSplit_eq_drazinActiveKernelSplit
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    (W : HasModularSpectralWedge E)
    (comp : IsCompatibleDPDWedge (E := E) CIK W)
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
    generalizedKL_activeShapeTerm (α := α) μ ν
      + generalizedKL_kernelMassTerm (α := α) μ ν
      ∧
    W.activeProjector = (1 : EndH) - CIK.spectralComplementaryProjector
      ∧
    CIK.spectralComplementaryProjector = W.PZero := by
  refine ⟨?_, ?_, comp.2.2⟩
  · simpa [generalizedKL_activeShapeTerm, generalizedKL_kernelMassTerm] using
      generalizedKL_scale_shape_split (α := α) μ ν
  · unfold HasModularSpectralWedge.activeProjector
    apply eq_sub_iff_add_eq.mpr
    calc
      W.PiPlus + W.PiMinus + CIK.spectralComplementaryProjector
          = W.PiPlus + W.PiMinus + W.PZero := by
              simp [comp.2.2]
      _ = (1 : EndH) := by
            simpa [add_assoc] using W.resolution

/--
Strengthened scale/shape bridge: besides the KL decomposition and
`P_0`/active-sector alignment, this packages the DPD generator identification
`2G = ε_wedge` and the projected supercharge wedge-commutator form on the same
compatible lane.
-/
@[rep_depth transport, capstone]
theorem relativeModularScaleShapeSplit_eq_drazinActiveKernelSplit_with_dilationGap
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    (W : HasModularSpectralWedge E)
    (comp : IsCompatibleDPDWedge (E := E) CIK W)
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
    generalizedKL_activeShapeTerm (α := α) μ ν
      + generalizedKL_kernelMassTerm (α := α) μ ν
      ∧
    W.activeProjector = (1 : EndH) - CIK.spectralComplementaryProjector
      ∧
    CIK.spectralComplementaryProjector = W.PZero
      ∧
    (2 : ℝ) • CIK.dilationGap = W.wedgeSign
      ∧
    CIK.dilationGap = ((2 : ℝ)⁻¹) • W.wedgeSign
      ∧
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralProjector W.wedgeSign := by
  rcases
      relativeModularScaleShapeSplit_eq_drazinActiveKernelSplit
        (E := E) (α := α) CIK W comp μ ν with
    ⟨hSplit, hActive, hZero⟩
  refine ⟨hSplit, hActive, hZero, ?_, ?_, ?_⟩
  · exact IsCompatibleDPDWedge.two_smul_dilationGap_eq_wedgeSign
      (E := E) (CIK := CIK) (W := W) comp
  · exact IsCompatibleDPDWedge.dilationGap_eq_half_wedgeSign
      (E := E) (CIK := CIK) (W := W) comp
  · exact IsCompatibleDPDWedge.projected_supercharge_eq_commutator_PD_wedgeSign
      (E := E) (CIK := CIK) (W := W) comp

/--
Locked comparison theorem:
the Drazin block decomposition of a relative modular operator candidate matches
the strict-positive projective/gauge split package on the same compatible lane.

Operatorially:
`RMO = Q_D RMO Q_D + P_D RMO P_D`.
Scalar/projective:
`gKL = shape + mass`.
-/
@[rep_depth transport, capstone]
theorem relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    (W : HasModularSpectralWedge E)
    (comp : IsCompatibleDPDWedge (E := E) CIK W)
    (RMO : EndH)
    (hQD_RMO_PD_zero :
      CIK.spectralComplementaryProjector * RMO * CIK.spectralProjector = 0)
    (hPD_RMO_QD_zero :
      CIK.spectralProjector * RMO * CIK.spectralComplementaryProjector = 0)
    (μ ν : PositiveMeasure α ℝ) :
    RMO
      =
    IsCompatibleDPDWedge.relativeModularKernelScalePart (CIK := CIK) RMO
      +
    IsCompatibleDPDWedge.relativeModularActiveShapePart (CIK := CIK) RMO
      ∧
    generalizedKL (α := α) μ ν
      =
    generalizedKL_activeShapeTerm (α := α) μ ν
      + generalizedKL_kernelMassTerm (α := α) μ ν
      ∧
    W.activeProjector = (1 : EndH) - CIK.spectralComplementaryProjector
      ∧
    CIK.spectralComplementaryProjector = W.PZero := by
  have hOp :
      RMO
        =
      IsCompatibleDPDWedge.relativeModularKernelScalePart (CIK := CIK) RMO
        +
      IsCompatibleDPDWedge.relativeModularActiveShapePart (CIK := CIK) RMO := by
    exact IsCompatibleDPDWedge.relativeModular_scaleShapeSplit
      (CIK := CIK)
      (hQD_RMO_PD_zero := hQD_RMO_PD_zero)
      (hPD_RMO_QD_zero := hPD_RMO_QD_zero)
  rcases
      relativeModularScaleShapeSplit_eq_drazinActiveKernelSplit
        (E := E) (α := α) CIK W comp μ ν with
    ⟨hKL, hActive, hZero⟩
  exact ⟨hOp, hKL, hActive, hZero⟩

/--
Wedge-calibrated CP-002 comparison theorem:
the operator-level split is discharged from the canonical-flow commutation
property, so no manual off-diagonal hypotheses are needed.
-/
@[rep_depth transport, capstone]
theorem relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit_of_wedgeCalibrated
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    (W : HasModularSpectralWedge E)
    (comp : IsCompatibleDPDWedge (E := E) CIK W)
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := InfoGeometry.Krein.spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ)
    (μ ν : PositiveMeasure α ℝ) :
    canonicalRelativeModularOperator (E := E) CIK τ
      =
    IsCompatibleDPDWedge.relativeModularKernelScalePart
      (CIK := CIK) (canonicalRelativeModularOperator (E := E) CIK τ)
      +
    IsCompatibleDPDWedge.relativeModularActiveShapePart
      (CIK := CIK) (canonicalRelativeModularOperator (E := E) CIK τ)
      ∧
    generalizedKL (α := α) μ ν
      =
    generalizedKL_activeShapeTerm (α := α) μ ν
      + generalizedKL_kernelMassTerm (α := α) μ ν
      ∧
    W.activeProjector = (1 : EndH) - CIK.spectralComplementaryProjector
      ∧
    CIK.spectralComplementaryProjector = W.PZero := by
  have hComm :
      Commute
        (canonicalRelativeModularOperator (E := E) CIK τ)
        CIK.spectralProjector :=
    canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ
  have hBlocks :
      CIK.spectralComplementaryProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralProjector
        = 0
        ∧
      CIK.spectralProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralComplementaryProjector
        = 0 :=
    relativeModular_block_diagonal (E := E) (CIK := CIK)
      (R := canonicalRelativeModularOperator (E := E) CIK τ) hComm.symm
  exact
    relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit
      (E := E) (α := α) CIK W comp
      (canonicalRelativeModularOperator (E := E) CIK τ)
      hBlocks.1 hBlocks.2 μ ν

end DrazinModularScaleShape

section PositiveRayCompatibility

variable {α : Type*}
variable [Fintype α] [Nonempty α]
variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- Canonical embedding of a strict-positive ray into the widened projective substrate. -/
noncomputable abbrev positiveRayToProjectiveState (q : PositiveRay α) : ProjectiveState α :=
  toProjectiveState (α := α) q

/--
On the strict-positive slice, the widened projective logarithmic generator is
almost everywhere the relative modular potential.
-/
@[rep_depth projective]
theorem positiveRay_logGenerator_eq_relativeModularPotential_ae
    (q q0 : PositiveRay α) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (positiveRayToProjectiveState (α := α) q0)
        (positiveRayToProjectiveState (α := α) q)
      =ᶠ[ae (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.gaugeSectionFinProb
            (α := α) q).toMeasure]
        fun a => relativeModularPotential (α := α) q q0 a := by
  exact
    InfoGeometry.Canonical.RelativePotentialDiscreteBridge.projectiveLogGenerator_eq_relativeModularPotential_ae
      (α := α) (q := q) (q0 := q0)

/--
Pointwise strict-positive compatibility: projective logarithmic generator equals
relative modular potential.
-/
@[rep_depth projective, simp]
theorem positiveRay_logGenerator_eq_relativeModularPotential
    (q q0 : PositiveRay α) (a : α) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (positiveRayToProjectiveState (α := α) q0)
        (positiveRayToProjectiveState (α := α) q) a
      = relativeModularPotential (α := α) q q0 a := by
  exact
    InfoGeometry.Canonical.RelativePotentialDiscreteBridge.projectiveLogGenerator_eq_relativeModularPotential
      (α := α) (q := q) (q0 := q0) a

/--
Equivalent pointwise form: projective logarithmic generator equals the negative
relative log-density.
-/
@[rep_depth projective, simp]
theorem positiveRay_logGenerator_eq_neg_relativeLogDensity
    (q q0 : PositiveRay α) (a : α) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (positiveRayToProjectiveState (α := α) q0)
        (positiveRayToProjectiveState (α := α) q) a
      = -relativeLogDensity (α := α) q q0 a := by
  rw [positiveRay_logGenerator_eq_relativeModularPotential (α := α) (q := q) (q0 := q0)
      (a := a)]
  exact relativeModularPotential_eq_neg_relativeLogDensity (α := α) q q0 a

/--
Weyl order parameter as the logarithmic representative of the relative modular
potential.

This is just a naming alias for the positive-ray projective logarithmic
generator theorem.
-/
@[rep_depth projective, simp]
theorem weylOrderParameter_eq_relativeModularPotential
    (q q0 : PositiveRay α) (a : α) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (positiveRayToProjectiveState (α := α) q0)
        (positiveRayToProjectiveState (α := α) q) a
      = relativeModularPotential (α := α) q q0 a := by
  exact
    positiveRay_logGenerator_eq_relativeModularPotential
      (α := α) (q := q) (q0 := q0) (a := a)

/--
Weyl order parameter as the negative logarithmic density cocycle.

This records the additive `-log` form of the positive density/modular cocycle.
-/
@[rep_depth projective, simp]
theorem weylOrderParameter_eq_neg_relativeLogDensity
    (q q0 : PositiveRay α) (a : α) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (positiveRayToProjectiveState (α := α) q0)
        (positiveRayToProjectiveState (α := α) q) a
      = -relativeLogDensity (α := α) q q0 a := by
  exact
    positiveRay_logGenerator_eq_neg_relativeLogDensity
      (α := α) (q := q) (q0 := q0) (a := a)

end PositiveRayCompatibility

end InfoGeometry.Canonical.ModularKLDivergenceBridge
