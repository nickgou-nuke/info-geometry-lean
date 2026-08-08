import InfoGeometry.Canonical.ReferenceSectorGaugeBridge
import InfoGeometry.Canonical.ModularTwoStateCorrelation
import InfoGeometry.Canonical.VortexAnomalyLink

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.VortexReferenceGaugeBridge

Canonical source/sink specialization of the spectroscopic gauge-fixing bridge.

This file is a thin consumer of the generic projector-sector gauge bridge and
the canonical vortex pair. It makes the degenerate-reference story explicit in
the doubled Majorana source/sink language.
-/

namespace InfoGeometry.Canonical.VortexReferenceGaugeBridge

open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.ReferenceSectorGaugeBridge
open InfoGeometry.Canonical.ModularTwoStateCorrelation
open InfoGeometry.Canonical.SpinorModularBridge
open InfoGeometry.Canonical.VortexAnomalyLink
open InfoGeometry.Krein
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.RealMajorana

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable def sourceProj : EndH := (canonicalVortexPair (E := E)).source
noncomputable def sinkProj : EndH := (canonicalVortexPair (E := E)).sink

/--
If the potential datum is degenerate on the canonical source sector, then the
anchored comparison gap is independent of which source-sector anchor is chosen.
-/
@[rep_depth transport] theorem twoStateGap_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    twoStateGap (E := E) P reference₀ comparison
      =
    twoStateGap (E := E) P reference₁ comparison := by
  exact twoStateGap_eq_of_projectorSectorDegeneracy
    (E := E) P (sourceProj (E := E)) reference₀ reference₁ comparison hDeg h₀ h₁

/--
If the potential datum is degenerate on the canonical sink sector, then the
anchored comparison gap is independent of which sink-sector anchor is chosen.
-/
@[rep_depth transport] theorem twoStateGap_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    twoStateGap (E := E) P reference₀ comparison
      =
    twoStateGap (E := E) P reference₁ comparison := by
  exact twoStateGap_eq_of_projectorSectorDegeneracy
    (E := E) P (sinkProj (E := E)) reference₀ reference₁ comparison hDeg h₀ h₁

/--
Under source-sector degeneracy, the relational functional shift is independent
of which source anchor is chosen.
-/
@[rep_depth transport] theorem functionalShift_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    functionalShift (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    functionalShift (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  exact functionalShift_eq_of_projectorSectorDegeneracy
    (E := E) P (sourceProj (E := E)) reference₀ reference₁ comparison hDeg h₀ h₁

/--
Under sink-sector degeneracy, the relational functional shift is independent of
which sink anchor is chosen.
-/
@[rep_depth transport] theorem functionalShift_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    functionalShift (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    functionalShift (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  exact functionalShift_eq_of_projectorSectorDegeneracy
    (E := E) P (sinkProj (E := E)) reference₀ reference₁ comparison hDeg h₀ h₁

/--
The comparison-state metric readout can be stated directly in source-sector
gauge language.
-/
@[rep_depth transport] theorem comparisonMetricReadout_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  exact ReferenceSectorGaugeBridge.comparisonMetricReadout_eq_of_projectorSectorDegeneracy
    (E := E) P (sourceProj (E := E)) reference₀ reference₁ comparison A hDeg h₀ h₁

/--
The comparison-state phase readout can be stated directly in source-sector
gauge language.
-/
@[rep_depth transport] theorem comparisonPhaseReadout_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  exact ReferenceSectorGaugeBridge.comparisonPhaseReadout_eq_of_projectorSectorDegeneracy
    (E := E) P (sourceProj (E := E)) reference₀ reference₁ comparison A hDeg h₀ h₁

/--
The comparison-state metric readout can be stated directly in sink-sector
gauge language.
-/
@[rep_depth transport] theorem comparisonMetricReadout_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  exact ReferenceSectorGaugeBridge.comparisonMetricReadout_eq_of_projectorSectorDegeneracy
    (E := E) P (sinkProj (E := E)) reference₀ reference₁ comparison A hDeg h₀ h₁

/--
The comparison-state phase readout can be stated directly in sink-sector
gauge language.
-/
@[rep_depth transport] theorem comparisonPhaseReadout_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  exact ReferenceSectorGaugeBridge.comparisonPhaseReadout_eq_of_projectorSectorDegeneracy
    (E := E) P (sinkProj (E := E)) reference₀ reference₁ comparison A hDeg h₀ h₁

/--
Under source-sector degeneracy, the comparison-state metric readout of the
canonical source vortex seed is independent of the chosen source anchor.
-/
@[rep_depth transport] theorem comparisonMetricReadout_sourceVortexSeed_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison)
        (sourceVortexSeed (E := E) V)
      =
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison)
        (sourceVortexSeed (E := E) V) := by
  exact comparisonMetricReadout_eq_of_sourceSectorDegeneracy
    (E := E) P reference₀ reference₁ comparison (sourceVortexSeed (E := E) V) hDeg h₀ h₁

/--
Under source-sector degeneracy, the comparison-state phase readout of the
canonical source vortex seed is independent of the chosen source anchor.
-/
@[rep_depth transport] theorem comparisonPhaseReadout_sourceVortexSeed_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison)
        (sourceVortexSeed (E := E) V)
      =
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison)
        (sourceVortexSeed (E := E) V) := by
  exact comparisonPhaseReadout_eq_of_sourceSectorDegeneracy
    (E := E) P reference₀ reference₁ comparison (sourceVortexSeed (E := E) V) hDeg h₀ h₁

/--
Under sink-sector degeneracy, the comparison-state metric readout of the
canonical sink vortex seed is independent of the chosen sink anchor.
-/
@[rep_depth transport] theorem comparisonMetricReadout_sinkVortexSeed_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison)
        (sinkVortexSeed (E := E) V)
      =
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison)
        (sinkVortexSeed (E := E) V) := by
  exact comparisonMetricReadout_eq_of_sinkSectorDegeneracy
    (E := E) P reference₀ reference₁ comparison (sinkVortexSeed (E := E) V) hDeg h₀ h₁

/--
Under sink-sector degeneracy, the comparison-state phase readout of the
canonical sink vortex seed is independent of the chosen sink anchor.
-/
@[rep_depth transport] theorem comparisonPhaseReadout_sinkVortexSeed_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison)
        (sinkVortexSeed (E := E) V)
      =
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison)
        (sinkVortexSeed (E := E) V) := by
  exact comparisonPhaseReadout_eq_of_sinkSectorDegeneracy
    (E := E) P reference₀ reference₁ comparison (sinkVortexSeed (E := E) V) hDeg h₀ h₁

/--
Under source-sector degeneracy, the infinitesimal phase-shifted channel
correlation against the canonical source vortex seed is independent of the
chosen source anchor.
-/
@[rep_depth transport] theorem
    deriv_comparisonTransportPhaseShiftedChannelCorrelation_sourceVortexSeed_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (reference₀ reference₁ comparison : H₂)
    (X : PerturbationChannel E)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    deriv
      (fun t =>
        comparisonTransportPhaseShiftedChannelCorrelation (E := E)
          (toRelationalInformationDatum (E := E) P reference₀ comparison)
          X (sourceVortexSeed (E := E) V) t)
      0
      =
    deriv
      (fun t =>
        comparisonTransportPhaseShiftedChannelCorrelation (E := E)
          (toRelationalInformationDatum (E := E) P reference₁ comparison)
          X (sourceVortexSeed (E := E) V) t)
      0 := by
  rw [deriv_comparisonTransportPhaseShiftedChannelCorrelation_at_zero_eq_comparisonMetricReadout,
    deriv_comparisonTransportPhaseShiftedChannelCorrelation_at_zero_eq_comparisonMetricReadout]
  have hReadout :=
    comparisonMetricReadout_sourceVortexSeed_eq_of_sourceSectorDegeneracy
      (E := E) P V reference₀ reference₁ comparison hDeg h₀ h₁
  simpa using
    congrArg
      (fun B =>
        B comparison ((channelPhaseAxis (E := E) X) comparison))
      hReadout

/--
Under sink-sector degeneracy, the infinitesimal phase-shifted channel
correlation against the canonical sink vortex seed is independent of the chosen
sink anchor.
-/
@[rep_depth transport] theorem
    deriv_comparisonTransportPhaseShiftedChannelCorrelation_sinkVortexSeed_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (reference₀ reference₁ comparison : H₂)
    (X : PerturbationChannel E)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    deriv
      (fun t =>
        comparisonTransportPhaseShiftedChannelCorrelation (E := E)
          (toRelationalInformationDatum (E := E) P reference₀ comparison)
          X (sinkVortexSeed (E := E) V) t)
      0
      =
    deriv
      (fun t =>
        comparisonTransportPhaseShiftedChannelCorrelation (E := E)
          (toRelationalInformationDatum (E := E) P reference₁ comparison)
          X (sinkVortexSeed (E := E) V) t)
      0 := by
  rw [deriv_comparisonTransportPhaseShiftedChannelCorrelation_at_zero_eq_comparisonMetricReadout,
    deriv_comparisonTransportPhaseShiftedChannelCorrelation_at_zero_eq_comparisonMetricReadout]
  have hReadout :=
    comparisonMetricReadout_sinkVortexSeed_eq_of_sinkSectorDegeneracy
      (E := E) P V reference₀ reference₁ comparison hDeg h₀ h₁
  simpa using
    congrArg
      (fun B =>
        B comparison ((channelPhaseAxis (E := E) X) comparison))
      hReadout

section BoundaryReadout

variable {A B : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [FiniteDimensional ℝ E]
variable [FiniteDimensional ℝ (DoubledSpace E)]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

/--
Source-side packaging: from nonzero transported central charge with boundary
identified to the source seed, obtain a localized source/sink property together
with source-seed derivative readout anchor invariance.
-/
@[rep_depth transport] theorem
    exists_sourceSinkSeedLocalizedVortex_and_deriv_sourceVortexSeed_eq_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (Xk : RealSplitKreinDiracFredholmModule A B H₂)
    (hXk : ChiralFredholmSurface Xk)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V Xk.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V Xk t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V Xk t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V Xk.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V Xk.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) Xk hXk ≠ 0)
    (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V)
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (X : PerturbationChannel E)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
      sourceVortexSeed (E := E) V v ≠ 0 ∧
      sinkVortexSeed (E := E) V v ≠ 0 ∧
      deriv
        (fun t =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₀ comparison)
            X (sourceVortexSeed (E := E) V) t)
        0
        =
      deriv
        (fun t =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₁ comparison)
            X (sourceVortexSeed (E := E) V) t)
        0 := by
  rcases
      exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V Xk hXk hEven t M P0 S hA hplus hminus
        hodd hBoundaryOnZeroModes hCentral hSource with
    ⟨v, hv⟩
  have hDeriv :
      deriv
        (fun t =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₀ comparison)
            X (sourceVortexSeed (E := E) V) t)
        0
        =
      deriv
        (fun t =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₁ comparison)
            X (sourceVortexSeed (E := E) V) t)
        0 :=
    deriv_comparisonTransportPhaseShiftedChannelCorrelation_sourceVortexSeed_eq_of_sourceSectorDegeneracy
      (E := E) P V reference₀ reference₁ comparison X hDeg h₀ h₁
  exact ⟨v, hv.1, hv.2.1, hv.2.2, hDeriv⟩

/--
Sink-side packaging: from nonzero transported central charge with boundary
identified to the sink seed, obtain a localized source/sink property together
with sink-seed derivative readout anchor invariance.
-/
@[rep_depth transport] theorem
    exists_sourceSinkSeedLocalizedVortex_and_deriv_sinkVortexSeed_eq_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (Xk : RealSplitKreinDiracFredholmModule A B H₂)
    (hXk : ChiralFredholmSurface Xk)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V Xk.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V Xk t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V Xk t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V Xk.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V Xk.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) Xk hXk ≠ 0)
    (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V)
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (X : PerturbationChannel E)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
      sourceVortexSeed (E := E) V v ≠ 0 ∧
      sinkVortexSeed (E := E) V v ≠ 0 ∧
      deriv
        (fun t =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₀ comparison)
            X (sinkVortexSeed (E := E) V) t)
        0
        =
      deriv
        (fun t =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₁ comparison)
            X (sinkVortexSeed (E := E) V) t)
        0 := by
  rcases
      exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V Xk hXk hEven t M P0 S hA hplus hminus
        hodd hBoundaryOnZeroModes hCentral hSink with
    ⟨v, hv⟩
  have hDeriv :
      deriv
        (fun t =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₀ comparison)
            X (sinkVortexSeed (E := E) V) t)
        0
        =
      deriv
        (fun t =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₁ comparison)
            X (sinkVortexSeed (E := E) V) t)
        0 :=
    deriv_comparisonTransportPhaseShiftedChannelCorrelation_sinkVortexSeed_eq_of_sinkSectorDegeneracy
      (E := E) P V reference₀ reference₁ comparison X hDeg h₀ h₁
  exact ⟨v, hv.1, hv.2.1, hv.2.2, hDeriv⟩

 /--
 Source-side kernel-separation variant of the boundary-readout package.
 -/
 @[rep_depth transport] theorem
     exists_sourceSinkSeedLocalizedVortex_and_deriv_sourceVortexSeed_eq_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
     (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
     (Xk : RealSplitKreinDiracFredholmModule A B H₂)
     (hXk : ChiralFredholmSurface Xk)
     (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
     (t : ℝ)
     (M : RealMajoranaDatum (S := H₂))
     (P0 : KPolarization (S := H₂) M)
     (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
     (hA : S.kernel.A = quasilatticeDirac V Xk.F t)
     (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V Xk t)
     (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V Xk t)
     (hodd :
       PolarizationOdd (M := M) P0 (quasilatticeDirac V Xk.F t))
     (hSep :
       (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
         = (⊥ : Submodule ℝ H₂))
     (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) Xk hXk ≠ 0)
     (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V)
     (P : PotentialDatum (E := E))
     (reference₀ reference₁ comparison : H₂)
     (X : PerturbationChannel E)
     (hDeg :
       ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
         value (E := E) P ψ = value (E := E) P χ)
     (h₀ : sourceProj (E := E) reference₀ = reference₀)
     (h₁ : sourceProj (E := E) reference₁ = reference₁) :
     ∃ v : H₂,
       IsDanglingZeroMode S v ∧
       sourceVortexSeed (E := E) V v ≠ 0 ∧
       sinkVortexSeed (E := E) V v ≠ 0 ∧
       deriv
         (fun t =>
           comparisonTransportPhaseShiftedChannelCorrelation (E := E)
             (toRelationalInformationDatum (E := E) P reference₀ comparison)
             X (sourceVortexSeed (E := E) V) t)
         0
         =
       deriv
         (fun t =>
           comparisonTransportPhaseShiftedChannelCorrelation (E := E)
             (toRelationalInformationDatum (E := E) P reference₁ comparison)
             X (sourceVortexSeed (E := E) V) t)
         0 := by
   rcases
       exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
         (A := A) (B := B) (E := E) V Xk hXk hEven t M P0 S hA hplus hminus
         hodd hSep hCentral hSource with
     ⟨v, hv⟩
   have hDeriv :
       deriv
         (fun t =>
           comparisonTransportPhaseShiftedChannelCorrelation (E := E)
             (toRelationalInformationDatum (E := E) P reference₀ comparison)
             X (sourceVortexSeed (E := E) V) t)
         0
         =
       deriv
         (fun t =>
           comparisonTransportPhaseShiftedChannelCorrelation (E := E)
             (toRelationalInformationDatum (E := E) P reference₁ comparison)
             X (sourceVortexSeed (E := E) V) t)
         0 :=
     deriv_comparisonTransportPhaseShiftedChannelCorrelation_sourceVortexSeed_eq_of_sourceSectorDegeneracy
       (E := E) P V reference₀ reference₁ comparison X hDeg h₀ h₁
   exact ⟨v, hv.1, hv.2.1, hv.2.2, hDeriv⟩

 /--
 Sink-side kernel-separation variant of the boundary-readout package.
 -/
 @[rep_depth transport] theorem
     exists_sourceSinkSeedLocalizedVortex_and_deriv_sinkVortexSeed_eq_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
     (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
     (Xk : RealSplitKreinDiracFredholmModule A B H₂)
     (hXk : ChiralFredholmSurface Xk)
     (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
     (t : ℝ)
     (M : RealMajoranaDatum (S := H₂))
     (P0 : KPolarization (S := H₂) M)
     (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
     (hA : S.kernel.A = quasilatticeDirac V Xk.F t)
     (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V Xk t)
     (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V Xk t)
     (hodd :
       PolarizationOdd (M := M) P0 (quasilatticeDirac V Xk.F t))
     (hSep :
       (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
         = (⊥ : Submodule ℝ H₂))
     (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) Xk hXk ≠ 0)
     (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V)
     (P : PotentialDatum (E := E))
     (reference₀ reference₁ comparison : H₂)
     (X : PerturbationChannel E)
     (hDeg :
       ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
         value (E := E) P ψ = value (E := E) P χ)
     (h₀ : sinkProj (E := E) reference₀ = reference₀)
     (h₁ : sinkProj (E := E) reference₁ = reference₁) :
     ∃ v : H₂,
       IsDanglingZeroMode S v ∧
       sourceVortexSeed (E := E) V v ≠ 0 ∧
       sinkVortexSeed (E := E) V v ≠ 0 ∧
       deriv
         (fun t =>
           comparisonTransportPhaseShiftedChannelCorrelation (E := E)
             (toRelationalInformationDatum (E := E) P reference₀ comparison)
             X (sinkVortexSeed (E := E) V) t)
         0
         =
       deriv
         (fun t =>
           comparisonTransportPhaseShiftedChannelCorrelation (E := E)
             (toRelationalInformationDatum (E := E) P reference₁ comparison)
             X (sinkVortexSeed (E := E) V) t)
         0 := by
   rcases
       exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
         (A := A) (B := B) (E := E) V Xk hXk hEven t M P0 S hA hplus hminus
         hodd hSep hCentral hSink with
     ⟨v, hv⟩
   have hDeriv :
       deriv
         (fun t =>
           comparisonTransportPhaseShiftedChannelCorrelation (E := E)
             (toRelationalInformationDatum (E := E) P reference₀ comparison)
             X (sinkVortexSeed (E := E) V) t)
         0
         =
       deriv
         (fun t =>
           comparisonTransportPhaseShiftedChannelCorrelation (E := E)
             (toRelationalInformationDatum (E := E) P reference₁ comparison)
             X (sinkVortexSeed (E := E) V) t)
         0 :=
     deriv_comparisonTransportPhaseShiftedChannelCorrelation_sinkVortexSeed_eq_of_sinkSectorDegeneracy
       (E := E) P V reference₀ reference₁ comparison X hDeg h₀ h₁
   exact ⟨v, hv.1, hv.2.1, hv.2.2, hDeriv⟩

 end BoundaryReadout

end Core

end InfoGeometry.Canonical.VortexReferenceGaugeBridge
