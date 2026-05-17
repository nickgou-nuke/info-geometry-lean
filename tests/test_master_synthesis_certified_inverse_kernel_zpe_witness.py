from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_certified_inverse_kernel_zpe_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private theorem "
        "bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_of_matchedHelicityWitness_of_zpeGravityWitness"
    )
    assert anchor in text
    block = text.split(anchor, 1)[1].split(
        "/--\nCertified-kernel capstone routed entirely through proof-carrying owner packets.",
        1,
    )[0]
    assert "(hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)" in block
    assert "(hRankPos : 0 < Module.finrank ℝ E)" not in block
    assert "(hEin : IsEinsteinKaehlerAtWith c R Kgeo x)" not in block

    owner_block = text.split(
        "private theorem bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_ownerWitnesses",
        1,
    )[1].split(
        "/--\nRegularization-sourced capstone wrapper:",
        1,
    )[0]
    assert (
        "bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_of_matchedHelicityWitness_of_zpeGravityWitness"
        in owner_block
    )
