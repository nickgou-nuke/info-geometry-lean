from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_kms_closure_pairing_fluid_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private def bits_to_gravity_to_fluid_capstone_cocycle_sourced_"
        "sinkhornKMSClosure_pairingFluidWitness"
    )
    assert anchor in text
    block = text.split(anchor, 1)[1].split(
        "/--\nKMS-closure / pairing-witness cocycle-sourced capstone variant with the\n"
        "ZPE/gravity owner packet.",
        1,
    )[0]
    assert "(Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)" in block
    assert "(hReg : RegularizationWitness" not in block
    assert "(hHelicity : MatchedHelicityWitness" not in block
    assert "bits_to_gravity_to_fluid_capstone_cocycle_sourced_sinkhornKMSClosure_pairingWitness" in block
    assert "(hReg := Wfluid.regularization)" in block
    assert "(hHelicity := Wfluid.helicity)" in block
