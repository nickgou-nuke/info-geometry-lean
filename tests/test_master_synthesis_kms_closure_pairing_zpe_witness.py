from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_kms_closure_pairing_zpe_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private def bits_to_gravity_to_fluid_capstone_cocycle_sourced_"
        "sinkhornKMSClosure_pairingWitness_of_zpeGravityWitness"
    )
    assert anchor in text
    block = text.split(anchor, 1)[1].split(
        "/--\nKMS-control / pairing-witness cocycle-sourced capstone variant:", 1
    )[0]
    assert "(hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)" in block
    assert "(hRankPos : 0 < Module.finrank ℝ E)" not in block
    assert "(hEin : IsEinsteinKaehlerAtWith c R Kgeo x)" not in block
    assert "bits_to_gravity_to_fluid_capstone_cocycle_sourced_sinkhornKMSClosure_pairingWitness" in block
    assert "(hRankPos := hZPEGravity.hRankPos)" in block
    assert "(hEin := hZPEGravity.hEin)" in block
