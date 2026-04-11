import InfoGeometry.Clifford.SplitQ11PhaseFlip
import InfoGeometry.Canonical.CentralChargeKKTParityBridge
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Canonical.SplitCliffordHeadSuperBracket
import InfoGeometry.Canonical.TopologicalResidue
import InfoGeometry.Canonical.VortexReferenceGaugeBridge
import InfoGeometry.Quantum.SuperchargeMultiplet
import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TopologicalInvariantInvariance

Canonical invariance/coherence surface for currently-owned topological quantities.

This file is intentionally a transport layer:
- it does not create new index owners;
- it records the split `Cl(1,1)` phase-flip invariants already proved at the
  Clifford owner level;
- it re-exports the operatorial KK analytical-index invariance already proved
  for quasilattice transport.
-/

namespace InfoGeometry.Canonical.TopologicalInvariantInvariance

section SplitQ11

open InfoGeometry.Clifford.SplitQ11PhaseFlip

/-- The split-null CAR relation is invariant under the canonical phase flip. -/
@[rep_depth transport]
theorem nullCAR_phaseFlip_invariant :
    (phaseFlipAlg nullMinus) * (phaseFlipAlg nullPlus)
      + (phaseFlipAlg nullPlus) * (phaseFlipAlg nullMinus) = 1 := by
  calc
    (phaseFlipAlg nullMinus) * (phaseFlipAlg nullPlus)
        + (phaseFlipAlg nullPlus) * (phaseFlipAlg nullMinus)
      = nullPlus * nullMinus + nullMinus * nullPlus := by
          rw [phaseFlip_apply_nullMinus, phaseFlip_apply_nullPlus]
    _ = 1 := by
          simpa [add_comm] using nullMinus_mul_nullPlus_add_swap

/-- Null nilpotency is preserved by the canonical phase flip. -/
@[rep_depth transport]
theorem nullMinus_sq_phaseFlip_invariant :
    (phaseFlipAlg nullMinus) * (phaseFlipAlg nullMinus) = 0 := by
  calc
    (phaseFlipAlg nullMinus) * (phaseFlipAlg nullMinus)
      = nullPlus * nullPlus := by rw [phaseFlip_apply_nullMinus]
    _ = 0 := by simpa using nullPlus_sq

/-- Null nilpotency is preserved by the canonical phase flip. -/
@[rep_depth transport]
theorem nullPlus_sq_phaseFlip_invariant :
    (phaseFlipAlg nullPlus) * (phaseFlipAlg nullPlus) = 0 := by
  calc
    (phaseFlipAlg nullPlus) * (phaseFlipAlg nullPlus)
      = nullMinus * nullMinus := by rw [phaseFlip_apply_nullPlus]
    _ = 0 := by simpa using nullMinus_sq

end SplitQ11

section DoubledCarrier

open InfoGeometry.Canonical.TopologicalResidue
open InfoGeometry.Quantum

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/--
On the canonical doubled carrier, the modular residue vanishes for the
canonical supercharge multiplet.
-/
@[rep_depth transport]
theorem canonical_wittenIndexResidue_eq_zero :
    wittenIndexResidue (E := E)
      (Quantum.canonicalSuperchargeMultiplet.inst (E := E)) = 0 := by
  simpa using
    (wittenIndexResidue_eq_zero (E := E)
      (Quantum.canonicalSuperchargeMultiplet.inst (E := E)))

end DoubledCarrier

section FixedVsTransportedConventions

open InfoGeometry.Canonical.ProjectorEquivariance

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Fixed-frame convention map:
the canonical phase flip on the grading involution swaps the two chiral
projectors.
-/
@[rep_depth transport]
theorem fixedGrading_phaseFlip_projectorSwap :
    ProjectorEquivariance.plusProjectorAfterPhaseFlip (E := E)
      =
    ProjectorEquivariance.minusProjector (E := E)
      ∧
    ProjectorEquivariance.minusProjectorAfterPhaseFlip (E := E)
      =
    ProjectorEquivariance.plusProjector (E := E) := by
  simpa using (ProjectorEquivariance.fixedGrading_projectorSwap (E := E))

end FixedVsTransportedConventions

section KK

open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.ModularTwoStateCorrelation
open InfoGeometry.Canonical.VortexAnomalyLink
open InfoGeometry.Canonical.SpinorModularBridge
open InfoGeometry.Canonical.CentralChargeKKTParityBridge
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.VortexReferenceGaugeBridge
open InfoGeometry.Krein
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.RealMajorana

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Operatorial quasilattice transport preserves the Fredholm/chiral analytical
index between any two time slices.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_transport_invariant
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (s t : ℝ) :
    quasilatticeAnalyticalIndex V X s
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s)
      =
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
  simpa using quasilatticeAnalyticalIndex_eq (E := E) V X hX hEven s t

/--
Scalar-shadow readout on the root lane:
the transported quasilattice analytical index is exactly the operatorial
central charge.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX := by
  exact operatorialCentralCharge_eq_transport_slice
    (A := A) (B := B) (E := E) V X hX hEven t

/--
Two-frame convention packet at one time slice:
- transported-frame index equals the operatorial central charge;
- fixed-frame phase flip swaps `P+` and `P-`.
-/
@[rep_depth transport]
theorem transportedIndex_fixedFrameConvention_map
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX
      ∧
    ProjectorEquivariance.plusProjectorAfterPhaseFlip (E := E)
      =
    ProjectorEquivariance.minusProjector (E := E)
      ∧
    ProjectorEquivariance.minusProjectorAfterPhaseFlip (E := E)
      =
    ProjectorEquivariance.plusProjector (E := E) := by
  refine ⟨?_, ?_, ?_⟩
  · exact quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t
  · simpa using (ProjectorEquivariance.plusProjectorAfterPhaseFlip_eq_minusProjector (E := E))
  · simpa using (ProjectorEquivariance.minusProjectorAfterPhaseFlip_eq_plusProjector (E := E))

section BoundaryReadout

variable [FiniteDimensional ℝ E]

/--
Topological-to-singular scalar obstruction bridge:
if the transported analytical index is nonzero, then the singular boundary
scale is nonzero under identified transported polarization.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_boundaryScale_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0) :
    S.boundaryScale ≠ 0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    intro hZero
    apply hIndexNonzero
    rw [quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t]
    exact hZero
  exact
    boundaryScale_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral

/--
Kernel-separation variant of the topological-to-singular scalar obstruction
bridge.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_boundaryScale_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0) :
    S.boundaryScale ≠ 0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    intro hZero
    apply hIndexNonzero
    rw [quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t]
    exact hZero
  exact
    boundaryScale_ne_zero_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hSep hCentral

/--
Parity-to-singular scalar obstruction bridge:
if the `Z₂` shadow of the operatorial central charge is nonzero, then the
singular boundary scale is nonzero under identified transported polarization.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_ne_zero_boundaryScale_ne_zero_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0) :
    S.boundaryScale ≠ 0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  exact
    boundaryScale_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral

/--
Parity/KKT/source-sink package under identified transported polarization:
nonzero central-charge parity yields

1. nonzero singular boundary scale,
2. transported chiral-kernel mismatch,
3. KKT odd split of the same Dirac phase,
4. grade-zero odd-odd commutator on that split.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_ne_zero_boundaryScale_and_kkt_package_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    S.boundaryScale ≠ 0
      ∧
    InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
      (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
    X.F =
      InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F
      + InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F
      ∧
    InfoGeometry.Canonical.KKTCore.IsGZero X.cl11
      (InfoGeometry.Canonical.KKTCore.commutator
        (InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F)
        (InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F)) := by
  have hBoundary :
      S.boundaryScale ≠ 0 :=
    operatorialCentralChargeParity_ne_zero_boundaryScale_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hParity
  have hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  rcases centralCharge_nonzero_forces_dimMismatch_and_kkt_odd_split
      (A := A) (B := B) (E := E) V X hX hEven t hCentral hGrade with
    ⟨hMismatch, hSplit, hCommutatorZero⟩
  exact ⟨hBoundary, hMismatch, hSplit, hCommutatorZero⟩

/--
Parity/KKT/head-superbracket package under identified transported polarization:
it extends the parity-to-boundary/KKT packet by adjoining the head split
`Cl(1,1)` null-mode CAR package and head `J/K` commutator closure.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_ne_zero_boundaryScale_kkt_and_headSuperBracket_package_of_identifiedTransportedPolarization
    (n : ℕ)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    S.boundaryScale ≠ 0
      ∧
    InfoGeometry.Canonical.ChiralDefectIndexBridge.TransportedChiralKernelDimMismatch
      (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
    X.F =
      InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F
      + InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F
      ∧
    InfoGeometry.Canonical.KKTCore.IsGZero X.cl11
      (InfoGeometry.Canonical.KKTCore.commutator
        (InfoGeometry.Canonical.KKTCore.gOnePart X.cl11 X.F)
        (InfoGeometry.Canonical.KKTCore.gNegOnePart X.cl11 X.F))
      ∧
    InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n
      * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n = 0
      ∧
    InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n
      * InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n = 0
      ∧
    InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headAnticommutator
      (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullMinus n)
      (InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headNullPlus n) = 1
      ∧
    InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.headCommutator
      (InfoGeometry.Canonical.SplitCliffordHeadLift.headJTensor n)
      (InfoGeometry.Canonical.SplitCliffordHeadLift.headKTensor n)
      = (2 : ℝ) • InfoGeometry.Canonical.SplitCliffordHeadLift.headEpsTensor n := by
  rcases
      operatorialCentralChargeParity_ne_zero_boundaryScale_and_kkt_package_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hParity hGrade with
    ⟨hBoundary, hMismatch, hSplit, hCommutatorZero⟩
  rcases InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.head_null_car_algebra n with
    ⟨hNullMinusSq, hNullPlusSq, hCAR⟩
  exact ⟨hBoundary, hMismatch, hSplit, hCommutatorZero, hNullMinusSq, hNullPlusSq,
    hCAR, InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.head_jk_commutator n⟩

/--
Kernel-separation parity variant:
nonzero `Z₂` central-charge shadow implies nonzero singular boundary scale under
identified transported polarization and kernel-separation.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_ne_zero_boundaryScale_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0) :
    S.boundaryScale ≠ 0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  exact
    boundaryScale_ne_zero_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hSep hCentral

/--
Parity-to-localized-vortex bridge:
if the `Z₂` shadow of the operatorial central charge is nonzero, then under
identified transported polarization the singular boundary package carries a
localized boundary vortex witness.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_ne_zero_exists_localizedBoundaryVortex_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0) :
    ∃ v : H₂, IsDanglingZeroMode S v ∧ coriolisVorticity S v ≠ 0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  exact
    exists_localizedBoundaryVortex_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral

/--
Kernel-separation parity-to-localized-vortex bridge.
-/
@[rep_depth transport]
theorem operatorialCentralChargeParity_ne_zero_exists_localizedBoundaryVortex_of_kernelSeparation_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0) :
    ∃ v : H₂, IsDanglingZeroMode S v ∧ coriolisVorticity S v ≠ 0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  exact
    exists_localizedBoundaryVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hSep hCentral

/--
Topological-to-boundary package (source side): if the transported analytical
index is nonzero, then under source boundary identification we obtain both a
localized source/sink seed witness and source-seed derivative readout
anchor-invariance.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_sourceBoundaryReadout_package
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0)
    (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V)
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (Xch : PerturbationChannel E)
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
        (fun s =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₀ comparison)
            Xch (sourceVortexSeed (E := E) V) s)
        0
        =
      deriv
        (fun s =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₁ comparison)
            Xch (sourceVortexSeed (E := E) V) s)
        0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    intro hZero
    apply hIndexNonzero
    rw [quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t]
    exact hZero
  exact
    exists_sourceSinkSeedLocalizedVortex_and_deriv_sourceVortexSeed_eq_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral hSource P reference₀ reference₁ comparison Xch hDeg h₀ h₁

/--
Topological-to-boundary package (sink side): if the transported analytical
index is nonzero, then under sink boundary identification we obtain both a
localized source/sink seed witness and sink-seed derivative readout
anchor-invariance.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_sinkBoundaryReadout_package
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0)
    (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V)
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (Xch : PerturbationChannel E)
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
        (fun s =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₀ comparison)
            Xch (sinkVortexSeed (E := E) V) s)
        0
        =
      deriv
        (fun s =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₁ comparison)
            Xch (sinkVortexSeed (E := E) V) s)
        0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    intro hZero
    apply hIndexNonzero
    rw [quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t]
    exact hZero
  exact
    exists_sourceSinkSeedLocalizedVortex_and_deriv_sinkVortexSeed_eq_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral hSink P reference₀ reference₁ comparison Xch hDeg h₀ h₁

/--
Source-identified commutator readout:
if the transported analytical index is nonzero and the boundary generator is
identified with the source seed, then the grading-axis transport commutator is
nonzero.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_transportCommutator_spectral_epsilon_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0)
    (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    intro hZero
    apply hIndexNonzero
    rw [quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t]
    exact hZero
  rcases
      exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hCentral hSource with
    ⟨v, _, hSourcev, _⟩
  have hSourceSeedNonzero : sourceVortexSeed (E := E) V ≠ 0 := by
    intro hZero
    exact hSourcev (by simp [hZero])
  exact
    (sourceVortexSeed_ne_zero_iff_transportCommutator_spectral_epsilon_ne_zero V).1
      hSourceSeedNonzero

/--
Sink-identified commutator readout:
if the transported analytical index is nonzero and the boundary generator is
identified with the sink seed, then the grading-axis transport commutator is
nonzero.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_transportCommutator_spectral_epsilon_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0)
    (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    intro hZero
    apply hIndexNonzero
    rw [quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t]
    exact hZero
  rcases
      exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hCentral hSink with
    ⟨v, _, _, hSinkv⟩
  have hSinkSeedNonzero : sinkVortexSeed (E := E) V ≠ 0 := by
    intro hZero
    exact hSinkv (by simp [hZero])
  exact
    (sinkVortexSeed_ne_zero_iff_transportCommutator_spectral_epsilon_ne_zero V).1
      hSinkSeedNonzero

/--
Kernel-separation source-side variant of the topological-to-boundary package.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_sourceBoundaryReadout_package_of_kernelSeparation
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0)
    (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V)
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (Xch : PerturbationChannel E)
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
        (fun s =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₀ comparison)
            Xch (sourceVortexSeed (E := E) V) s)
        0
        =
      deriv
        (fun s =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₁ comparison)
            Xch (sourceVortexSeed (E := E) V) s)
        0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    intro hZero
    apply hIndexNonzero
    rw [quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t]
    exact hZero
  exact
    exists_sourceSinkSeedLocalizedVortex_and_deriv_sourceVortexSeed_eq_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hSep hCentral hSource P reference₀ reference₁ comparison Xch hDeg h₀ h₁

/--
Kernel-separation sink-side variant of the topological-to-boundary package.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_ne_zero_sinkBoundaryReadout_package_of_kernelSeparation
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := H₂))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      InfoGeometry.Quantum.BulkBoundary.PolarizationOdd
        (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hIndexNonzero :
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) ≠ 0)
    (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V)
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (Xch : PerturbationChannel E)
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
        (fun s =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₀ comparison)
            Xch (sinkVortexSeed (E := E) V) s)
        0
        =
      deriv
        (fun s =>
          comparisonTransportPhaseShiftedChannelCorrelation (E := E)
            (toRelationalInformationDatum (E := E) P reference₁ comparison)
            Xch (sinkVortexSeed (E := E) V) s)
        0 := by
  have hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 := by
    intro hZero
    apply hIndexNonzero
    rw [quasilatticeAnalyticalIndex_eq_operatorialCentralCharge
      (A := A) (B := B) (E := E) V X hX hEven t]
    exact hZero
  exact
    exists_sourceSinkSeedLocalizedVortex_and_deriv_sinkVortexSeed_eq_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hSep hCentral hSink P reference₀ reference₁ comparison Xch hDeg h₀ h₁

end BoundaryReadout

end KK

end InfoGeometry.Canonical.TopologicalInvariantInvariance
