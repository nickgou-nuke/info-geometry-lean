import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Physics.Thermodynamics.ChiralSimilarityKMSBridge

/-!
# Chiral similarity KMS bridge

Canonical re-export of the verified chiral similarity KMS readout layer.
This bridge adds no new analytic claim; it only forwards the physics owner.
-/

namespace InfoGeometry.Canonical.ChiralSimilarityKMSBridge

open InfoGeometry.Physics
open InfoGeometry.Physics.Thermodynamics

noncomputable def modularParameter := InfoGeometry.Physics.Thermodynamics.modularParameter

theorem modular_time_triality_root :
    InfoGeometry.Physics.Thermodynamics.modularParameter (2 * Real.pi / 3) ^ 3 = 1 :=
  InfoGeometry.Physics.Thermodynamics.modular_time_triality_root

abbrev InvariantReadout := InfoGeometry.Physics.Thermodynamics.InvariantReadout

def chiralTrace : BdGBlock ℝ → ℝ :=
  InfoGeometry.Physics.Thermodynamics.chiralTrace

theorem chiralTrace_flow_invariant (mu : ℝ)
    (X : BdGBlock ℝ) :
    chiralTrace (InfoGeometry.Physics.Thermodynamics.chiralSimilarityFlow mu X) =
      chiralTrace X :=
  InfoGeometry.Physics.Thermodynamics.chiralTrace_flow_invariant mu X

def traceInvariantReadout : InvariantReadout :=
  InfoGeometry.Physics.Thermodynamics.traceInvariantReadout

noncomputable def chiralSimilarityKMSReadoutDatum
    (beta : ℝ) (hbeta : 0 < beta) :
    InfoGeometry.OperatorAlgebra.HorizonKMS.KMSReadoutDatum
      (BdGBlock ℝ) :=
  InfoGeometry.Physics.Thermodynamics.chiralSimilarityKMSReadoutDatum beta hbeta

namespace InvariantReadout

noncomputable def toKMSReadoutDatum
    (R : InvariantReadout) (beta : ℝ) (hbeta : 0 < beta) :
    InfoGeometry.OperatorAlgebra.HorizonKMS.KMSReadoutDatum
      (BdGBlock ℝ) :=
  InfoGeometry.Physics.Thermodynamics.InvariantReadout.toKMSReadoutDatum R beta hbeta

end InvariantReadout

end InfoGeometry.Canonical.ChiralSimilarityKMSBridge
