import InfoGeometry.Canonical.TopologicalInvariantInvariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv

Thin closure layer for the boundary-localization lane:

- converts the scalar obstruction readout (`boundaryScale ≠ 0`) into the
  operator obstruction (`boundaryGenerator ≠ 0`),
- then exports direct quasilattice-index / parity to boundary-generator
  nonvanishing statements.

This file introduces no new owners; it composes already-owned bridges.
-/

namespace InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv

open InfoGeometry.Canonical
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.CentralChargeKKTParityBridge
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.SingularBoundaryCorrection
open InfoGeometry.Canonical.TopologicalInvariantInvariance
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.RealMajorana

section Core

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Nonvanishing scalar boundary obstruction is equivalent to nonvanishing boundary
generator.
-/
@[rep_depth transport]
theorem boundaryScale_ne_zero_iff_boundaryGenerator_ne_zero
    (S : SingularBoundaryCorrection E) :
    S.boundaryScale ≠ 0 ↔ S.boundaryGenerator ≠ 0 := by
  exact not_congr S.boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero

end Core

section TransportedBoundary

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Direct boundary-generator readout:
nonzero transported analytical index forces nonzero singular boundary generator
under identified transported polarization.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_boundaryGenerator_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂, quasilatticeDirac V X.F t v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0) :
    S.boundaryGenerator ≠ 0 := by
  have hScale :
      S.boundaryScale ≠ 0 :=
    quasilatticeAnalyticalIndex_ne_zero_boundaryScale_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t
      M P0 S hA hplus hminus hodd hBoundaryOnZeroModes hIndexNonzero
  exact (boundaryScale_ne_zero_iff_boundaryGenerator_ne_zero (S := S)).mp hScale

/--
Kernel-separation variant of direct boundary-generator readout.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_boundaryGenerator_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0) :
    S.boundaryGenerator ≠ 0 := by
  have hScale :
      S.boundaryScale ≠ 0 :=
    quasilatticeAnalyticalIndex_ne_zero_boundaryScale_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t
      M P0 S hA hplus hminus hodd hSep hIndexNonzero
  exact (boundaryScale_ne_zero_iff_boundaryGenerator_ne_zero (S := S)).mp hScale

/--
Parity-lifted direct boundary-generator readout:
nonzero `Z₂` central-charge shadow forces nonzero singular boundary generator.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_ne_zero_boundaryGenerator_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂, quasilatticeDirac V X.F t v = 0 → v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0) :
    S.boundaryGenerator ≠ 0 := by
  have hScale :
      S.boundaryScale ≠ 0 :=
    operatorialCentralChargeParity_ne_zero_boundaryScale_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t
      M P0 S hA hplus hminus hodd hBoundaryOnZeroModes hParity
  exact (boundaryScale_ne_zero_iff_boundaryGenerator_ne_zero (S := S)).mp hScale

/--
Kernel-separation parity variant of direct boundary-generator readout.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_ne_zero_boundaryGenerator_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0) :
    S.boundaryGenerator ≠ 0 := by
  have hScale :
      S.boundaryScale ≠ 0 :=
    operatorialCentralChargeParity_ne_zero_boundaryScale_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t
      M P0 S hA hplus hminus hodd hSep hParity
  exact (boundaryScale_ne_zero_iff_boundaryGenerator_ne_zero (S := S)).mp hScale

end TransportedBoundary

end InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv
