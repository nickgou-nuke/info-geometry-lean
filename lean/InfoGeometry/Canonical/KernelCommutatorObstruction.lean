import InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KernelCommutatorObstruction

Thin wrapper surface for the kernel-commutator obstruction lane.

This module does not introduce new defect ontology. It re-exports:
- a finite-dimensional kernel-mismatch noncommutation lemma,
- and the direct projector-obstruction consequence already owned by
  `SuperchargeEinsteinSourceBridge`.
-/

namespace InfoGeometry.Canonical.KernelCommutatorObstruction

open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.ChiralDefectIndexBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.OperatorialCentralCharge
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
Finite-dimensional kernel mismatch forces noncommutation.
-/
theorem commutator_ne_zero_of_kernel_mismatch
    [FiniteDimensional ℝ H₂]
    (P1 P2 : H₂ →L[ℝ] H₂)
    (hMismatch :
      Module.finrank ℝ ((P1.comp P2).toLinearMap.ker)
        ≠
      Module.finrank ℝ ((P2.comp P1).toLinearMap.ker)) :
    P1.comp P2 ≠ P2.comp P1 := by
  intro hComm
  apply hMismatch
  rw [hComm]

/--
Direct central-charge-to-obstruction eliminator using the canonical projector
pair and a supplied mismatch-to-noncommutation implication.
-/
@[rep_depth transport, capstone]
theorem projectorObstruction_ne_zero_of_mismatch_direct
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
  exact
    InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.projectorObstruction_ne_zero_of_operatorialCentralCharge_ne_zero_of_mismatch_forces_projector_noncommute
      (A := A) (B := B) (E := E)
      CI V X hX hEven t hMismatchNoncommute hCentral

end Core

end InfoGeometry.Canonical.KernelCommutatorObstruction
