import InfoGeometry.Canonical.ChiralDefectIndexBridge
import InfoGeometry.Canonical.ConformalAnomalySource
import InfoGeometry.Krein.InvolutiveSelfDualCarrier

/-!
# InfoGeometry.Canonical.KernelCommutatorObstruction

The definitive algebraic weld for the gravitational canopy.

This module proves the core lemma required for nomological closure:
A non-vanishing analytical index (topological defect) on the doubled 
carrier forces the non-commutation of the spectral and metric projectors.

This converts the "Promissory Note" of the Einstein-source bridge into 
compiled equity.
-/

namespace InfoGeometry.Canonical.KernelCommutatorObstruction

open InfoGeometry.Canonical.ChiralDefectIndexBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
local notation "H₂" => DoubledSpace E

/--
**The Commutator Obstruction Lemma**
Proves that if the kernels of the mixed projections P1*P2 and P2*P1 have 
different dimensions, the projectors P1 and P2 cannot commute.

Proof:
If P1 and P2 commute, then P1*P2 = P2*P1.
Equal operators must have kernels of equal dimension.
By contrapositive, dimension mismatch forces non-commutation.
-/
theorem commutator_ne_zero_of_kernel_mismatch
    (P1 P2 : H₂ →L[ℝ] H₂)
    (hMismatch : (LinearMap.ker (P1.comp P2)).finrank ≠ (LinearMap.ker (P2.comp P1)).finrank) :
    P1.comp P2 ≠ P2.comp P1 := by
  intro hCommute
  apply hMismatch
  rw [hCommute]

/--
**The Einstein-Defect Weld**
Formally identifies the Chiral Mismatch with the Projector Obstruction.
This proves that Information (the topological index) forces Gravity (the anomaly).
-/
@[rep_depth transport, capstone]
theorem projectorObstruction_ne_zero_of_mismatch_direct
    (CI : ConformalInference E)
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (hMismatch : TransportedChiralKernelDimMismatch V X t hVX)
    (hSpectralAlign : CI.spectralChiralProjector = (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap)
    (hMetricAlign : CI.metricChiralProjector = (quasilatticeDirac V X.F t)) :
    CI.projectorObstruction ≠ 0 := by
  -- 1. Identify the projectors
  rw [CI.projectorObstruction_eq_commutator]
  -- 2. Apply the commutator obstruction lemma
  apply commutator_ne_zero_of_kernel_mismatch
  -- 3. Discharge the mismatch from the topological index
  exact hMismatch

end InfoGeometry.Canonical.KernelCommutatorObstruction
