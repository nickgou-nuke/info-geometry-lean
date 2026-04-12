import InfoGeometry.Canonical.ConformalAnomalySource
import InfoGeometry.Canonical.ChiralDefectIndexBridge
import InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv
import InfoGeometry.Canonical.SingularBoundaryCorrection
import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge

Thin bridge from the transported defect lane to the conformal Einstein-source
lane.

This file keeps the bridge honest: the only new ingredient is an explicit
compatibility witness saying how transported chiral-kernel mismatch forces
projector noncommutation on the conformal surface. Everything else is reused
from existing owners.
-/

namespace InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge

open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.ChiralDefectIndexBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.ConformalUnification.ConformalInference
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

section Core

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Compatibility witness between the transported supercharge/defect lane and the
conformal projector lane.

Only the load-bearing implication is required: transported chiral-kernel
mismatch forces noncommutation of the conformal spectral/metric projectors.
-/
@[rep_depth transport]
structure SuperchargeProjectorCompatibility
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (superchargeProj transportedProj : E →L[ℝ] E) : Prop where
  spectralProj_eq_superchargeProj :
    CI.spectralChiralProjector = superchargeProj
  metricProj_eq_transportedProj :
    CI.metricChiralProjector = transportedProj
  mismatch_forces_projector_noncommute :
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX →
      CI.spectralChiralProjector * CI.metricChiralProjector
        ≠
      CI.metricChiralProjector * CI.spectralChiralProjector

/--
Under compatibility, transported chiral-kernel mismatch forces a nonzero
conformal projector obstruction.
-/
@[rep_depth transport]
theorem projectorObstruction_ne_zero_of_compat_of_mismatch
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (superchargeProj transportedProj : E →L[ℝ] E)
    (hCompat :
      SuperchargeProjectorCompatibility
        (A := A) (B := B) (E := E)
        CI V X t hVX superchargeProj transportedProj)
    (hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX) :
    CI.projectorObstruction ≠ 0 := by
  intro hObsZero
  have hCommute :
      Commute CI.spectralChiralProjector CI.metricChiralProjector :=
    (CI.projectorObstruction_eq_zero_iff_commute).1 hObsZero
  exact (hCompat.mismatch_forces_projector_noncommute hMismatch) hCommute.eq

/--
Under compatibility, transported chiral-kernel mismatch forces nonzero conformal
source scale.
-/
@[rep_depth transport]
theorem chiralScale_ne_zero_of_compat_of_mismatch
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (superchargeProj transportedProj : E →L[ℝ] E)
    (hCompat :
      SuperchargeProjectorCompatibility
        (A := A) (B := B) (E := E)
        CI V X t hVX superchargeProj transportedProj)
    (hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX) :
    CI.chiralScale ≠ 0 := by
  exact CI.chiralScale_ne_zero_of_projectors_not_commute
    (hCompat.mismatch_forces_projector_noncommute hMismatch)

/--
Mismatch-to-source Einstein bridge:
under compatibility, transported chiral-kernel mismatch yields nonzero conformal
source scale and the existing Einstein source equation.
-/
@[rep_depth transport]
theorem chiralScale_ne_zero_and_einsteinEquation_of_compat_of_mismatch
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (superchargeProj transportedProj : E →L[ℝ] E)
    (hCompat :
      SuperchargeProjectorCompatibility
        (A := A) (B := B) (E := E)
        CI V X t hVX superchargeProj transportedProj)
    (hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX)
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    CI.chiralScale ≠ 0
      ∧
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt
        Kgeo x CI.chiralScale) := by
  refine ⟨?_, ?_⟩
  · exact chiralScale_ne_zero_of_compat_of_mismatch
      (A := A) (B := B) (E := E) CI V X t hVX
      superchargeProj transportedProj hCompat hMismatch
  · exact CI.einsteinEquation_of_projectorObstruction_source
      (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin

/--
Central-charge to obstruction eliminator:
nonzero operatorial central charge, plus compatibility, forces nonzero conformal
projector obstruction.
-/
@[rep_depth transport]
theorem projectorObstruction_ne_zero_of_operatorialCentralCharge_ne_zero_of_compat
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (superchargeProj transportedProj : E →L[ℝ] E)
    (hCompat :
      SuperchargeProjectorCompatibility (A := A) (B := B) (E := E)
        CI V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        superchargeProj transportedProj)
    (hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    CI.projectorObstruction ≠ 0 := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX :=
    transportedChiralKernelDimMismatch_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven t hCentral
  exact projectorObstruction_ne_zero_of_compat_of_mismatch
    (A := A) (B := B) (E := E) CI V X t hVX
    superchargeProj transportedProj hCompat hMismatch

/--
Transported-index to obstruction eliminator:
nonzero transported analytical index, plus compatibility, forces nonzero
conformal projector obstruction.
-/
@[rep_depth transport]
theorem projectorObstruction_ne_zero_of_quasilatticeAnalyticalIndex_ne_zero_of_compat
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (superchargeProj transportedProj : E →L[ℝ] E)
    (hCompat :
      SuperchargeProjectorCompatibility
        (A := A) (B := B) (E := E)
        CI V X t hVX superchargeProj transportedProj)
    (hIndexNonzero : quasilatticeAnalyticalIndex V X t hVX ≠ 0) :
    CI.projectorObstruction ≠ 0 := by
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX :=
    transportedChiralKernelDimMismatch_of_quasilatticeAnalyticalIndex_ne_zero
      (A := A) (B := B) (E := E) V X t hVX hIndexNonzero
  exact projectorObstruction_ne_zero_of_compat_of_mismatch
    (A := A) (B := B) (E := E) CI V X t hVX
    superchargeProj transportedProj hCompat hMismatch

/--
Central-charge eliminator:
nonzero operatorial central charge, plus compatibility, yields nonzero conformal
source scale and the existing Einstein source equation.
-/
@[rep_depth transport]
theorem chiralScale_ne_zero_and_einsteinEquation_of_operatorialCentralCharge_ne_zero_of_compat
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (superchargeProj transportedProj : E →L[ℝ] E)
    (hCompat :
      SuperchargeProjectorCompatibility (A := A) (B := B) (E := E)
        CI V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        superchargeProj transportedProj)
    (hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    CI.chiralScale ≠ 0
      ∧
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt
        Kgeo x CI.chiralScale) := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX :=
    transportedChiralKernelDimMismatch_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven t hCentral
  exact chiralScale_ne_zero_and_einsteinEquation_of_compat_of_mismatch
    (A := A) (B := B) (E := E) CI V X t hVX
    superchargeProj transportedProj hCompat hMismatch
    (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin

/--
Transported-index eliminator:
nonzero transported analytical index, plus compatibility, yields nonzero
conformal source scale and the existing Einstein source equation.
-/
@[rep_depth transport]
theorem chiralScale_ne_zero_and_einsteinEquation_of_quasilatticeAnalyticalIndex_ne_zero_of_compat
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (superchargeProj transportedProj : E →L[ℝ] E)
    (hCompat :
      SuperchargeProjectorCompatibility
        (A := A) (B := B) (E := E)
        CI V X t hVX superchargeProj transportedProj)
    (hIndexNonzero : quasilatticeAnalyticalIndex V X t hVX ≠ 0)
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    CI.chiralScale ≠ 0
      ∧
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt
        Kgeo x CI.chiralScale) := by
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX :=
    transportedChiralKernelDimMismatch_of_quasilatticeAnalyticalIndex_ne_zero
      (A := A) (B := B) (E := E) V X t hVX hIndexNonzero
  exact chiralScale_ne_zero_and_einsteinEquation_of_compat_of_mismatch
    (A := A) (B := B) (E := E) CI V X t hVX
    superchargeProj transportedProj hCompat hMismatch
    (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin

/--
Standalone Einstein-source closure on the transported-index-mismatch lane.
-/
@[rep_depth transport]
theorem einsteinEquation_of_transportedIndexMismatch_source
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (superchargeProj transportedProj : E →L[ℝ] E)
    (hCompat :
      SuperchargeProjectorCompatibility
        (A := A) (B := B) (E := E)
        CI V X t hVX superchargeProj transportedProj)
    (hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX)
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt
        Kgeo x CI.chiralScale) := by
  exact
    (chiralScale_ne_zero_and_einsteinEquation_of_compat_of_mismatch
      (A := A) (B := B) (E := E) CI V X t hVX
      superchargeProj transportedProj hCompat hMismatch
      (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin).2

/--
Canonical projector-identity compatibility constructor:
if transported mismatch forces noncommutation of the conformal spectral/metric
projectors, then compatibility is obtained with the native projector pair
`(CI.spectralChiralProjector, CI.metricChiralProjector)`.
-/
@[rep_depth transport]
theorem superchargeProjectorCompatibility_of_mismatch_forces_projector_noncommute
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (hMismatchNoncommute :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector) :
    SuperchargeProjectorCompatibility (A := A) (B := B) (E := E)
      CI V X t hVX CI.spectralChiralProjector CI.metricChiralProjector := by
  refine ⟨rfl, rfl, ?_⟩
  intro hMismatch
  exact hMismatchNoncommute hMismatch

/--
Transported chiral-kernel mismatch implies nonzero transported analytical index
on the same quasilattice slice.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_of_transportedChiralKernelDimMismatch
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX) :
    quasilatticeAnalyticalIndex V X t hVX ≠ 0 := by
  classical
  intro hZero
  cases hVX with
  | mk hPlus hMinus =>
      letI := hPlus
      letI := hMinus
      have hEqInt :
          (Module.finrank ℝ (quasilatticeChiralKernelSlicePlus V X t) : ℤ)
            =
          (Module.finrank ℝ (quasilatticeChiralKernelSliceMinus V X t) : ℤ) := by
        exact sub_eq_zero.mp (by simpa [quasilatticeAnalyticalIndex] using hZero)
      exact hMismatch (Int.ofNat.inj hEqInt)

/--
Operator-algebraic kernel-to-commutator lemma:
if transported mismatch forces nonzero singular boundary scale, and the
conformal projector pair is identified with the singular-boundary projector
pair, then mismatch forces conformal projector noncommutation.
-/
@[rep_depth transport]
theorem mismatch_forces_projector_noncommute_of_boundaryScale_ne_zero
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection E)
    (hSpectralAlign : CI.spectralChiralProjector = S.spectralProjector)
    (hMetricAlign : CI.metricChiralProjector = S.leftProjector)
    (hBoundaryScaleNonzeroOfMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX →
        S.boundaryScale ≠ 0) :
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX →
      CI.spectralChiralProjector * CI.metricChiralProjector
        ≠
      CI.metricChiralProjector * CI.spectralChiralProjector := by
  intro hMismatch hComm
  have hBoundaryComm :
      S.spectralProjector * S.leftProjector
        = S.leftProjector * S.spectralProjector := by
    simpa [hSpectralAlign, hMetricAlign] using hComm
  have hBoundaryGeneratorZero : S.boundaryGenerator = 0 :=
    S.boundaryGenerator_eq_zero_of_projectors_commute hBoundaryComm
  have hBoundaryScaleZero : S.boundaryScale = 0 :=
    (S.boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero).2 hBoundaryGeneratorZero
  exact (hBoundaryScaleNonzeroOfMismatch hMismatch) hBoundaryScaleZero

/--
Carrier-identification lift:
noncommutation of the singular-boundary projector pair transfers to
noncommutation of the conformal projector pair whenever the two projector
families are identified.
-/
@[rep_depth transport]
theorem conformal_projector_noncommute_of_boundary_projector_noncommute_of_alignment
    (CI : ConformalInference E)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection E)
    (hSpectralAlign : CI.spectralChiralProjector = S.spectralProjector)
    (hMetricAlign : CI.metricChiralProjector = S.leftProjector)
    (hBoundaryNoncommute :
      S.spectralProjector * S.leftProjector
        ≠
      S.leftProjector * S.spectralProjector) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      ≠
    CI.metricChiralProjector * CI.spectralChiralProjector := by
  intro hComm
  apply hBoundaryNoncommute
  simpa [hSpectralAlign, hMetricAlign] using hComm

/--
Kernel-to-boundary-projector-commutator closure on the identified transported
polarization lane: transported chiral-kernel mismatch forces noncommutation of
the singular-boundary spectral/left projectors.
-/
@[rep_depth transport]
theorem mismatch_forces_boundary_projector_noncommute_of_identifiedTransportedPolarization
    [FiniteDimensional ℝ E]
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA :
      S.kernel.A =
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus :
      P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus :
      P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0) :
    TransportedChiralKernelDimMismatch
        (A := A) (B := B) (E := E)
        V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) →
      S.spectralProjector * S.leftProjector
        ≠
      S.leftProjector * S.spectralProjector := by
  intro hMismatch
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hIndexNonzero :
      quasilatticeAnalyticalIndex V X t hVX ≠ 0 :=
    quasilatticeAnalyticalIndex_ne_zero_of_transportedChiralKernelDimMismatch
      (A := A) (B := B) (E := E) V X t hVX hMismatch
  have hBoundaryGeneratorNonzero :
      S.boundaryGenerator ≠ 0 :=
    InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.quasilatticeAnalyticalIndex_ne_zero_boundaryGenerator_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hIndexNonzero
  intro hBoundaryComm
  have hBoundaryGeneratorZero : S.boundaryGenerator = 0 :=
    S.boundaryGenerator_eq_zero_of_projectors_commute hBoundaryComm
  exact hBoundaryGeneratorNonzero hBoundaryGeneratorZero

/--
Kernel-to-conformal-projector-commutator closure on the identified transported
polarization lane (boundary carrier form):
transported chiral-kernel mismatch forces noncommutation of the conformal
projectors once they are identified with the singular-boundary pair.
-/
@[rep_depth transport]
theorem mismatch_forces_conformal_projector_noncommute_of_identifiedTransportedPolarization_on_boundaryCarrier
    [FiniteDimensional ℝ E]
    (CI : ConformalInference H₂)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA :
      S.kernel.A =
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus :
      P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus :
      P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hSpectralAlign : CI.spectralChiralProjector = S.spectralProjector)
    (hMetricAlign : CI.metricChiralProjector = S.leftProjector) :
    TransportedChiralKernelDimMismatch
        (A := A) (B := B) (E := E)
        V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) →
      CI.spectralChiralProjector * CI.metricChiralProjector
        ≠
      CI.metricChiralProjector * CI.spectralChiralProjector := by
  intro hMismatch
  have hBoundaryNoncommute :
      S.spectralProjector * S.leftProjector
        ≠
      S.leftProjector * S.spectralProjector :=
    mismatch_forces_boundary_projector_noncommute_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E)
      V X hX hEven t M P0 S hA hplus hminus hodd hBoundaryOnZeroModes hMismatch
  intro hComm
  apply hBoundaryNoncommute
  simpa [hSpectralAlign, hMetricAlign] using hComm

/--
Kernel-commutator closure on the identified transported-polarization lane
(boundary carrier form):
nonzero transported analytical index forces noncommutation of the conformal
projectors.
-/
@[rep_depth transport]
theorem conformal_projector_noncommute_of_quasilatticeAnalyticalIndex_ne_zero_of_identifiedTransportedPolarization_on_boundaryCarrier
    [FiniteDimensional ℝ E]
    (CI : ConformalInference H₂)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA :
      S.kernel.A =
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus :
      P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus :
      P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hSpectralAlign : CI.spectralChiralProjector = S.spectralProjector)
    (hMetricAlign : CI.metricChiralProjector = S.leftProjector)
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      ≠
    CI.metricChiralProjector * CI.spectralChiralProjector := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX :=
    transportedChiralKernelDimMismatch_of_quasilatticeAnalyticalIndex_ne_zero
      (A := A) (B := B) (E := E) V X t hVX hIndexNonzero
  exact
    mismatch_forces_conformal_projector_noncommute_of_identifiedTransportedPolarization_on_boundaryCarrier
      (A := A) (B := B) (E := E)
      CI V X hX hEven t M P0 S hA hplus hminus hodd hBoundaryOnZeroModes
      hSpectralAlign hMetricAlign hMismatch

/--
Boundary-carrier compatibility witness between the transported defect lane and
the conformal projector lane.
-/
@[rep_depth transport]
structure SuperchargeBoundaryCarrierCompatibility
    [FiniteDimensional ℝ E]
    (CI : ConformalInference H₂)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (superchargeProj transportedProj : H₂ →L[ℝ] H₂) : Prop where
  spectralProj_eq_superchargeProj :
    CI.spectralChiralProjector = superchargeProj
  metricProj_eq_transportedProj :
    CI.metricChiralProjector = transportedProj
  mismatch_forces_projector_noncommute :
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX →
      CI.spectralChiralProjector * CI.metricChiralProjector
        ≠
      CI.metricChiralProjector * CI.spectralChiralProjector

/--
Boundary-carrier compatibility constructor on the identified
transported-polarization lane. This discharges the load-bearing
mismatch-to-noncommutation implication from existing owners.
-/
@[rep_depth transport]
theorem superchargeBoundaryCarrierCompatibility_of_identifiedTransportedPolarization
    [FiniteDimensional ℝ E]
    (CI : ConformalInference H₂)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA :
      S.kernel.A =
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus :
      P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus :
      P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hSpectralAlign : CI.spectralChiralProjector = S.spectralProjector)
    (hMetricAlign : CI.metricChiralProjector = S.leftProjector) :
    SuperchargeBoundaryCarrierCompatibility (A := A) (B := B) (E := E)
      CI V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      S.spectralProjector S.leftProjector := by
  refine ⟨hSpectralAlign, hMetricAlign, ?_⟩
  exact
    mismatch_forces_conformal_projector_noncommute_of_identifiedTransportedPolarization_on_boundaryCarrier
      (A := A) (B := B) (E := E)
      CI V X hX hEven t M P0 S hA hplus hminus hodd hBoundaryOnZeroModes
      hSpectralAlign hMetricAlign

/--
On the identified transported-polarization lane (boundary carrier form),
nonzero operatorial central charge forces noncommutation of the conformal
projectors.
-/
@[rep_depth transport]
theorem conformal_projector_noncommute_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization_on_boundaryCarrier
    [FiniteDimensional ℝ E]
    (CI : ConformalInference H₂)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA :
      S.kernel.A =
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus :
      P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus :
      P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hSpectralAlign : CI.spectralChiralProjector = S.spectralProjector)
    (hMetricAlign : CI.metricChiralProjector = S.leftProjector)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      ≠
    CI.metricChiralProjector * CI.spectralChiralProjector := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX :=
    transportedChiralKernelDimMismatch_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven t hCentral
  exact
    mismatch_forces_conformal_projector_noncommute_of_identifiedTransportedPolarization_on_boundaryCarrier
      (A := A) (B := B) (E := E)
      CI V X hX hEven t M P0 S hA hplus hminus hodd hBoundaryOnZeroModes
      hSpectralAlign hMetricAlign hMismatch

/--
On the identified transported-polarization lane (boundary carrier form),
nonzero operatorial central charge forces nonzero conformal source scale.
-/
@[rep_depth transport]
theorem chiralScale_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization_on_boundaryCarrier
    [FiniteDimensional ℝ E]
    (CI : ConformalInference H₂)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA :
      S.kernel.A =
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t)
    (hplus :
      P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus :
      P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0
        (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hSpectralAlign : CI.spectralChiralProjector = S.spectralProjector)
    (hMetricAlign : CI.metricChiralProjector = S.leftProjector)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    CI.chiralScale ≠ 0 := by
  exact
    CI.chiralScale_ne_zero_of_projectors_not_commute
      (conformal_projector_noncommute_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization_on_boundaryCarrier
        (A := A) (B := B) (E := E)
        CI V X hX hEven t M P0 S hA hplus hminus hodd hBoundaryOnZeroModes
        hSpectralAlign hMetricAlign hCentral)

/--
Compatibility constructor from singular-boundary scale forcing.
-/
@[rep_depth transport]
theorem superchargeProjectorCompatibility_of_boundaryScale_ne_zero_of_mismatch
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection E)
    (hSpectralAlign : CI.spectralChiralProjector = S.spectralProjector)
    (hMetricAlign : CI.metricChiralProjector = S.leftProjector)
    (hBoundaryScaleNonzeroOfMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX →
        S.boundaryScale ≠ 0) :
    SuperchargeProjectorCompatibility (A := A) (B := B) (E := E)
      CI V X t hVX S.spectralProjector S.leftProjector := by
  refine ⟨hSpectralAlign, hMetricAlign, ?_⟩
  exact mismatch_forces_projector_noncommute_of_boundaryScale_ne_zero
    (A := A) (B := B) (E := E)
    CI V X t hVX S hSpectralAlign hMetricAlign hBoundaryScaleNonzeroOfMismatch

/--
Central-charge to Einstein-source eliminator with canonical projector pair:
consumes only the mismatch-to-noncommutation implication and reuses all existing
owners.
-/
@[rep_depth transport]
theorem chiralScale_ne_zero_and_einsteinEquation_of_operatorialCentralCharge_ne_zero_of_mismatch_forces_projector_noncommute
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hMismatchNoncommute :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
          V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    CI.chiralScale ≠ 0
      ∧
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt
        Kgeo x CI.chiralScale) := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hCompat :
      SuperchargeProjectorCompatibility (A := A) (B := B) (E := E)
        CI V X t hVX CI.spectralChiralProjector CI.metricChiralProjector :=
    superchargeProjectorCompatibility_of_mismatch_forces_projector_noncommute
      (A := A) (B := B) (E := E) CI V X t hVX hMismatchNoncommute
  exact
    chiralScale_ne_zero_and_einsteinEquation_of_operatorialCentralCharge_ne_zero_of_compat
      (A := A) (B := B) (E := E) CI V X hX hEven t
      CI.spectralChiralProjector CI.metricChiralProjector
      hCompat hCentral
      (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin

/--
Central-charge to obstruction eliminator with canonical projector pair.
-/
@[rep_depth transport]
theorem projectorObstruction_ne_zero_of_operatorialCentralCharge_ne_zero_of_mismatch_forces_projector_noncommute
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hMismatchNoncommute :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
          V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    CI.projectorObstruction ≠ 0 := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hCompat :
      SuperchargeProjectorCompatibility (A := A) (B := B) (E := E)
        CI V X t hVX CI.spectralChiralProjector CI.metricChiralProjector :=
    superchargeProjectorCompatibility_of_mismatch_forces_projector_noncommute
      (A := A) (B := B) (E := E) CI V X t hVX hMismatchNoncommute
  exact
    projectorObstruction_ne_zero_of_operatorialCentralCharge_ne_zero_of_compat
      (A := A) (B := B) (E := E) CI V X hX hEven t
      CI.spectralChiralProjector CI.metricChiralProjector
      hCompat hCentral

/--
Transported-index to Einstein-source eliminator with canonical projector pair.
-/
@[rep_depth transport]
theorem chiralScale_ne_zero_and_einsteinEquation_of_quasilatticeAnalyticalIndex_ne_zero_of_mismatch_forces_projector_noncommute
    (CI : ConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (hMismatchNoncommute :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX →
        CI.spectralChiralProjector * CI.metricChiralProjector
          ≠
        CI.metricChiralProjector * CI.spectralChiralProjector)
    (hIndexNonzero : quasilatticeAnalyticalIndex V X t hVX ≠ 0)
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    CI.chiralScale ≠ 0
      ∧
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt
        Kgeo x CI.chiralScale) := by
  have hCompat :
      SuperchargeProjectorCompatibility (A := A) (B := B) (E := E)
        CI V X t hVX CI.spectralChiralProjector CI.metricChiralProjector :=
    superchargeProjectorCompatibility_of_mismatch_forces_projector_noncommute
      (A := A) (B := B) (E := E) CI V X t hVX hMismatchNoncommute
  exact
    chiralScale_ne_zero_and_einsteinEquation_of_quasilatticeAnalyticalIndex_ne_zero_of_compat
      (A := A) (B := B) (E := E) CI V X t hVX
      CI.spectralChiralProjector CI.metricChiralProjector
      hCompat hIndexNonzero
      (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin

end Core

end InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge
