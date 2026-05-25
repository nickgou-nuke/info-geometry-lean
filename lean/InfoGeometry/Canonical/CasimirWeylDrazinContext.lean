import InfoGeometry.Canonical.CentralChargeAnomaly
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.ModularSourceBridge
import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CasimirWeylDrazinContext

Operatorial context for the Casimir/Weyl/Drazin residual claim.

This module deliberately does not introduce a finite matrix model and does not
prove a zeta/Casimir formula.  The zeta-regularized Casimir residual and its
identification with an informational cosmological constant are represented as
explicit context fields.  The proved content is the repo-native operatorial
consequence: Drazin-cut stability, defect localization, regular-support
annihilation, and transport protection of the central-charge lane.
-/

namespace InfoGeometry.Canonical.CasimirWeylDrazinContext

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.ModularSourceBridge
open InfoGeometry.Canonical.ObserverDefect
open InfoGeometry.Canonical.RelativeModularScaleShapeSplit

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
Context surface for the claim that the zeta-regularized Casimir residual is the
informational cosmological constant on the operatorial Drazin/Weyl lane.

The equality is a hypothesis field.  The surrounding fields are the concrete
operatorial data needed to route the residual through the existing Drazin cut
and sourced modular generator.
-/
@[rep_depth transport]
structure CasimirWeylDrazinData (CIK : CertifiedInverseKernel H₂) where
  observer : ObserverL5 (E := E) CIK
  flow : BackgroundModularFlow (E := E) CIK
  zetaCasimirResidual : ℝ
  lambdaInfo : ℝ
  lambdaInfo_eq_zetaCasimirResidual :
    lambdaInfo = zetaCasimirResidual

namespace CasimirWeylDrazinData

/-- Drazin-core projector on the certified inverse-kernel lane. -/
@[rep_depth operator]
noncomputable abbrev drazinCoreProjector (CIK : CertifiedInverseKernel H₂) : EndH :=
  CertifiedInverseKernel.spectralProjector CIK

/-- Moore-Penrose metric projector: the Penrose representation of the shell. -/
@[rep_depth operator]
noncomputable abbrev penroseMetricProjector (CIK : CertifiedInverseKernel H₂) : EndH :=
  CertifiedInverseKernel.metricProjector CIK

/-- Complementary Drazin cut used by sourced defect residuals. -/
@[rep_depth operator]
noncomputable abbrev drazinComplementProjector (CIK : CertifiedInverseKernel H₂) : EndH :=
  CertifiedInverseKernel.spectralComplementaryProjector CIK

/-- Sourced modular generator on the Drazin/Weyl context lane. -/
@[rep_depth transport]
noncomputable def sourcedGenerator
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK) : EndH :=
  sourcedModularGenerator (E := E) CIK C.observer C.flow

/-- Regular-support compressed super-Hamiltonian on the Drazin projector lane. -/
@[rep_depth operator]
noncomputable def regularCoreHamiltonian
    (CIK : CertifiedInverseKernel H₂) : EndH :=
  CertifiedInverseKernel.regularRestrictedSuperHamiltonian CIK

/-- The informational cosmological constant is the declared Casimir residual. -/
@[rep_depth transport]
theorem lambdaInfo_eq_residual
    {CIK : CertifiedInverseKernel H₂}
    (C : CasimirWeylDrazinData (E := E) CIK) :
    C.lambdaInfo = C.zetaCasimirResidual :=
  C.lambdaInfo_eq_zetaCasimirResidual

/-- Critical stiffness is the residual mismatch after identifying `Λ`. -/
@[rep_depth transport]
noncomputable def criticalStiffness
    {CIK : CertifiedInverseKernel H₂}
    (C : CasimirWeylDrazinData (E := E) CIK) : ℝ :=
  C.lambdaInfo - C.zetaCasimirResidual

/--
Once the context identifies `Λ` with the zeta/Casimir residual, the critical
stiffness mismatch vanishes.
-/
@[rep_depth transport]
theorem criticalStiffness_eq_zero
    {CIK : CertifiedInverseKernel H₂}
    (C : CasimirWeylDrazinData (E := E) CIK) :
    C.criticalStiffness = 0 := by
  unfold criticalStiffness
  rw [C.lambdaInfo_eq_zetaCasimirResidual]
  simp

/--
The sourced modular generator respects the Drazin cut.  This is the operatorial
version of "the residual source is quarantined by the core/shell split".
-/
@[rep_depth transport]
theorem sourcedGenerator_respects_drazin_cut
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK) :
    Commute (sourcedGenerator (E := E) CIK C) CIK.spectralComplementaryProjector := by
  simpa [sourcedGenerator] using
    sourcedModularGenerator_respects_spectral_cut CIK C.observer C.flow

/--
Bulk lanes orthogonal to the Drazin-complement cut do not see the sourced
defect residual.
-/
@[rep_depth transport]
theorem sourcedGenerator_bulk_invariant
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (P : EndH)
    (hPQ0 : P * CIK.spectralComplementaryProjector = 0) :
    P * sourcedGenerator (E := E) CIK C * P = P * C.flow.K0 * P := by
  simpa [sourcedGenerator] using
    sourcedModularGenerator_bulk_invariant CIK C.observer C.flow P hPQ0

/--
The Drazin-complement lane absorbs exactly the sourced defect residual.
-/
@[rep_depth transport]
theorem sourcedGenerator_boundary_excitation
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK) :
    let Q0 := CIK.spectralComplementaryProjector
    Q0 * sourcedGenerator (E := E) CIK C * Q0
      = Q0 * C.flow.K0 * Q0 + observerDefectResidual CIK C.observer := by
  simpa [sourcedGenerator] using
    sourcedModularGenerator_boundary_excitation CIK C.observer C.flow

/--
The sourced generator collapses to the background flow exactly when the observer
 defect residual vanishes.
-/
@[rep_depth transport]
theorem sourcedGenerator_boundary_excitation_eq_background_iff_observerDefectResidual_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK) :
    CIK.spectralComplementaryProjector * sourcedGenerator (E := E) CIK C *
        CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector * C.flow.K0 * CIK.spectralComplementaryProjector
        ↔ observerDefectResidual CIK C.observer = 0 := by
  constructor
  · intro hEq
    have hBoundary := sourcedGenerator_boundary_excitation (E := E) CIK C
    dsimp at hBoundary
    have hSum :
        CIK.spectralComplementaryProjector * C.flow.K0 *
            CIK.spectralComplementaryProjector + observerDefectResidual CIK C.observer
          = CIK.spectralComplementaryProjector * C.flow.K0 *
              CIK.spectralComplementaryProjector + 0 := by
      exact hBoundary.symm.trans (by simpa [hEq])
    exact add_left_cancel hSum
  · intro hZero
    have hBoundary := sourcedGenerator_boundary_excitation (E := E) CIK C
    dsimp at hBoundary
    simpa [hZero] using hBoundary

/--
The sourced generator collapses to the background flow exactly when the observer
 defect residual vanishes.
-/
@[rep_depth transport]
theorem sourcedGenerator_eq_background_iff_observerDefectResidual_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK) :
    sourcedGenerator (E := E) CIK C = C.flow.K0
      ↔ observerDefectResidual CIK C.observer = 0 := by
  constructor
  · intro hEq
    have hEq' :
        C.flow.K0 + observerDefectResidual CIK C.observer = C.flow.K0 + 0 := by
      simpa [sourcedGenerator, sourcedModularGenerator] using hEq
    exact add_left_cancel hEq'
  · intro hZero
    simp [sourcedGenerator, sourcedModularGenerator, hZero]

/--
Under zero central defect, the Drazin-complement boundary excitation collapses to
its background block exactly when the exact owner-side `Z_D` deviation-control
predicate holds.
-/
@[rep_depth transport]
theorem sourcedGenerator_boundary_excitation_eq_background_iff_deviationControlledByZD_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    CIK.spectralComplementaryProjector * sourcedGenerator (E := E) CIK C *
        CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector * C.flow.K0 * CIK.spectralComplementaryProjector
        ↔ ObserverDeviationControlledByZD CIK C.observer := by
  have hResidualIffStrain :
      observerDefectResidual CIK C.observer = 0
        ↔ observerOrientationStrain CIK C.observer = 0 := by
    exact
      (observerOrientationStrain_eq_zero_iff
        (CIK := CIK) (obs := C.observer)).symm
  have hResidualIffControl :
      observerDefectResidual CIK C.observer = 0
        ↔ ObserverDeviationControlledByZD CIK C.observer := by
    exact
      hResidualIffStrain.trans
        (observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero
          (CIK := CIK) (obs := C.observer) hZD)
  exact
    (sourcedGenerator_boundary_excitation_eq_background_iff_observerDefectResidual_eq_zero
      (E := E) CIK C).trans hResidualIffControl

/--
Under zero central defect, exact owner-side `Z_D` deviation control forces the
Drazin-complement boundary excitation to collapse to its background block.
-/
@[rep_depth transport]
theorem sourcedGenerator_boundary_excitation_eq_background_of_deviationControlledByZD_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hControl : ObserverDeviationControlledByZD CIK C.observer)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    CIK.spectralComplementaryProjector * sourcedGenerator (E := E) CIK C *
        CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector * C.flow.K0 * CIK.spectralComplementaryProjector := by
  exact
    (sourcedGenerator_boundary_excitation_eq_background_iff_deviationControlledByZD_of_ZD_eq_zero
      (E := E) CIK C hZD).2 hControl

/--
Under zero central defect, Drazin-complement boundary excitation collapse is
already equivalent to the smaller owner-side scalarized observer strain witness.
This removes the larger explicit `ObserverDeviationControlledByZD` packet on the
exact zero-`Z_D` lane.
-/
@[rep_depth transport]
theorem sourcedGenerator_boundary_excitation_eq_background_iff_strain_eq_zero_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    CIK.spectralComplementaryProjector * sourcedGenerator (E := E) CIK C *
        CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector * C.flow.K0 * CIK.spectralComplementaryProjector
        ↔ observerOrientationStrain CIK C.observer = 0 := by
  exact
    (sourcedGenerator_boundary_excitation_eq_background_iff_deviationControlledByZD_of_ZD_eq_zero
      (E := E) CIK C hZD).trans
      (observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero
        (CIK := CIK) (obs := C.observer) hZD).symm

/--
Under zero central defect, zero scalarized observer strain constructively forces
Drazin-complement boundary excitation collapse to the background block.
-/
@[rep_depth transport]
theorem sourcedGenerator_boundary_excitation_eq_background_of_strain_eq_zero_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0)
    (hStrain : observerOrientationStrain CIK C.observer = 0) :
    CIK.spectralComplementaryProjector * sourcedGenerator (E := E) CIK C *
        CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector * C.flow.K0 * CIK.spectralComplementaryProjector := by
  exact
    (sourcedGenerator_boundary_excitation_eq_background_iff_strain_eq_zero_of_ZD_eq_zero
      (E := E) CIK C hZD).2 hStrain

/--
Compressed-deviation-zero is exactly the sourced-generator/background-collapse
surface on the owner lane. This removes the intermediate
`observerDefectResidual = 0` packet for callers that already own the smaller
compressed commutator witness.
-/
@[rep_depth transport]
theorem sourcedGenerator_eq_background_iff_compressedDeviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK) :
    sourcedGenerator (E := E) CIK C = C.flow.K0
      ↔ CIK.spectralComplementaryProjector *
          DrazinSupercharge.commutator
            (observerProjectorDeviation CIK C.observer) CIK.dilationGap *
          CIK.spectralComplementaryProjector = 0 := by
  constructor
  · intro hBackground
    have hResidual : observerDefectResidual CIK C.observer = 0 :=
      (sourcedGenerator_eq_background_iff_observerDefectResidual_eq_zero
        (E := E) CIK C).1 hBackground
    simpa [observerDefectResidual_eq_projectorCompression_commutator_deviation
      (CIK := CIK) (obs := C.observer)] using hResidual
  · intro hZero
    exact
      (sourcedGenerator_eq_background_iff_observerDefectResidual_eq_zero
        (E := E) CIK C).2
        (observerDefectResidual_eq_zero_of_compressedDeviation_eq_zero
          (CIK := CIK) (obs := C.observer) hZero)

/--
Compressed-deviation-zero is a constructive owner route forcing the sourced
generator to collapse to the background flow.
-/
@[rep_depth transport]
theorem sourcedGenerator_eq_background_of_compressedDeviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hZero :
      CIK.spectralComplementaryProjector *
        DrazinSupercharge.commutator
          (observerProjectorDeviation CIK C.observer) CIK.dilationGap *
        CIK.spectralComplementaryProjector = 0) :
    sourcedGenerator (E := E) CIK C = C.flow.K0 := by
  exact
    (sourcedGenerator_eq_background_iff_compressedDeviation_eq_zero
      (E := E) CIK C).2 hZero

/--
Zero central-defect budget plus owner control of the observer deviation forces
 the sourced generator to collapse to the background flow.
-/
@[rep_depth transport]
theorem sourcedGenerator_eq_background_of_deviationControlledByZD_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hControl : ObserverDeviationControlledByZD CIK C.observer)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    sourcedGenerator (E := E) CIK C = C.flow.K0 := by
  exact
    (sourcedGenerator_eq_background_iff_observerDefectResidual_eq_zero
      (E := E) CIK C).2
      (observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero
        (CIK := CIK) (obs := C.observer) hControl hZD)

/--
Under zero central defect, sourced-generator collapse is equivalent to the exact
owner-side `Z_D` deviation-control predicate.
-/
@[rep_depth transport]
theorem sourcedGenerator_eq_background_iff_deviationControlledByZD_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    sourcedGenerator (E := E) CIK C = C.flow.K0
      ↔ ObserverDeviationControlledByZD CIK C.observer := by
  have hResidualIffStrain :
      observerDefectResidual CIK C.observer = 0
        ↔ observerOrientationStrain CIK C.observer = 0 := by
    exact
      (observerOrientationStrain_eq_zero_iff
        (CIK := CIK) (obs := C.observer)).symm
  have hResidualIffControl :
      observerDefectResidual CIK C.observer = 0
        ↔ ObserverDeviationControlledByZD CIK C.observer := by
    exact
      hResidualIffStrain.trans
        (observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero
          (CIK := CIK) (obs := C.observer) hZD)
  exact
    (sourcedGenerator_eq_background_iff_observerDefectResidual_eq_zero
      (E := E) CIK C).trans hResidualIffControl

/--
Under zero central defect, sourced-generator collapse is equivalent to zero
scalarized observer strain. This narrows the explicit `ObserverDeviationControlledByZD`
packet to the smaller owner-side strain witness.
-/
@[rep_depth transport]
theorem sourcedGenerator_eq_background_iff_strain_eq_zero_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    sourcedGenerator (E := E) CIK C = C.flow.K0
      ↔ observerOrientationStrain CIK C.observer = 0 := by
  exact
    (sourcedGenerator_eq_background_iff_deviationControlledByZD_of_ZD_eq_zero
      (E := E) CIK C hZD).trans
      (observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero
        (CIK := CIK) (obs := C.observer) hZD).symm

/--
Under zero central defect, zero scalarized observer strain constructively forces
sourced-generator collapse to the background flow.
-/
@[rep_depth transport]
theorem sourcedGenerator_eq_background_of_strain_eq_zero_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (C : CasimirWeylDrazinData (E := E) CIK)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0)
    (hStrain : observerOrientationStrain CIK C.observer = 0) :
    sourcedGenerator (E := E) CIK C = C.flow.K0 := by
  exact
    (sourcedGenerator_eq_background_iff_strain_eq_zero_of_ZD_eq_zero
      (E := E) CIK C hZD).2 hStrain

/--
The regular Drazin-core Hamiltonian is supported on the Drazin projector and
annihilated by the complementary cut on both sides.
-/
@[rep_depth operator]
theorem regularCoreHamiltonian_support_flow_package
    (CIK : CertifiedInverseKernel H₂)
    (t : ℝ) :
    (CIK.spectralProjector * regularCoreHamiltonian (E := E) CIK
        = regularCoreHamiltonian (E := E) CIK)
      ∧ (regularCoreHamiltonian (E := E) CIK * CIK.spectralProjector
          = regularCoreHamiltonian (E := E) CIK)
      ∧ (CIK.toInformationCartanTriple.spectralAdjointFlow
            CIK.toInformationCartanTriple.GammaS t
            (regularCoreHamiltonian (E := E) CIK)
            = regularCoreHamiltonian (E := E) CIK)
      ∧ (CIK.spectralComplementaryProjector
            * CIK.toInformationCartanTriple.spectralAdjointFlow
                CIK.toInformationCartanTriple.GammaS t
                (regularCoreHamiltonian (E := E) CIK) = 0)
      ∧ (CIK.toInformationCartanTriple.spectralAdjointFlow
            CIK.toInformationCartanTriple.GammaS t
            (regularCoreHamiltonian (E := E) CIK)
            * CIK.spectralComplementaryProjector = 0) := by
  simpa [regularCoreHamiltonian] using
    CertifiedInverseKernel.regularRestrictedSuperHamiltonian_support_flow_package
      (CIK := CIK) t

/--
If a relative modular representative commutes with the Drazin projector, it
splits into complementary and active Drazin blocks.
-/
@[capstone, rep_depth transport]
theorem relativeModular_scaleShapeSplit_of_commute
    (CIK : CertifiedInverseKernel H₂)
    (_C : CasimirWeylDrazinData (E := E) CIK)
    {R : EndH}
    (hComm : Commute CIK.spectralProjector R) :
    R =
      CIK.spectralComplementaryProjector * (R * CIK.spectralComplementaryProjector)
        + CIK.spectralProjector * (R * CIK.spectralProjector) := by
  exact relativeModular_scaleShapeSplit (E := E) (CIK := CIK) (R := R) hComm

end CasimirWeylDrazinData

end Core

section CentralCharge

open InfoGeometry.Canonical.CentralChargeAnomaly
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Operatorial topological-protection bridge: a nonzero central charge prevents
every Bogoliubov/quasilattice transport slice from collapsing to zero
analytical index.
-/
@[rep_depth transport]
theorem transportSlice_ne_zero_of_centralCharge_ne_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (hCentral : centralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ≠ 0 := by
  exact CentralChargeAnomaly.transportSlice_ne_zero_of_centralCharge_ne_zero
    (A := A) (B := B) (E := E) V X hX hEven hCentral t

end CentralCharge

end InfoGeometry.Canonical.CasimirWeylDrazinContext
