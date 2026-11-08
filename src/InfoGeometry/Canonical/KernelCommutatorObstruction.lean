import InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

section OmitUnusedCommutatorInstances

omit [CompleteSpace E] [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

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

end OmitUnusedCommutatorInstances

/--
Direct central-charge-to-obstruction eliminator using the canonical projector
pair and a supplied mismatch-to-noncommutation implication.
-/
@[rep_depth transport, capstone]
alias projectorObstruction_ne_zero_of_mismatch_direct :=
  InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.projectorObstruction_ne_zero_of_operatorialCentralCharge_ne_zero_of_mismatch_forces_projector_noncommute

end Core

end InfoGeometry.Canonical.KernelCommutatorObstruction
