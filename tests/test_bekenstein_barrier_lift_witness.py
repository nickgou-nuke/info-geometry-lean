from pathlib import Path


LEAN = Path("lean/InfoGeometry/Canonical/BekensteinBound.lean")


def test_barrier_lift_witness_route_exists() -> None:
    text = LEAN.read_text()
    assert "structure BarrierLiftWitness" in text
    assert "theorem topologicalBekensteinBound_of_barrierLiftWitness" in text
    block = text.split("theorem topologicalBekensteinBound_of_barrierLiftWitness", 1)[1].split("/--", 1)[0]
    assert "(W : BarrierLiftWitness (n := n) (H := H) σ u T)" in block
    assert "(hBridge : ScalarCocycleBridge" not in block
    assert "(hBarrierLift : ∀ k : Nat, trajectoryRNBarrier n T k =" not in block
    assert "(hBridge := W.hBridge)" in block
    assert "(hBarrierLift := W.hBarrierLift)" in block
