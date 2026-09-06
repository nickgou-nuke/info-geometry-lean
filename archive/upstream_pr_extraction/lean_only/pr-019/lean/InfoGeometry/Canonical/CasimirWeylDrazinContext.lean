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
