import InfoGeometry.Projective.QDeformedTwistorAmplituhedronBridge
import InfoGeometry.Topology.GrandUnificationLinker

structure OnShellQResidueComputationDatum {Op : Type*} [Ring Op] [Star Op]
    (moving : ℕ) (jewel : InfoGeometry.QuantumJewel Op)
    extends InfoGeometry.Projective.QDeformedTwistorAmplituhedronDatum moving where

def test {Op : Type*} [Ring Op] [Star Op]
    {moving : ℕ} {jewel : InfoGeometry.QuantumJewel Op}
    (D : OnShellQResidueComputationDatum moving jewel) :
    InfoGeometry.Projective.KuzminQStableCarrier :=
  D.qStable
