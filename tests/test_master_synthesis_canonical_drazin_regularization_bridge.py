from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_canonical_drazin_regularization_bridge_theorem() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = "private theorem bridge_fluid_helicity_of_canonicalDrazinRegularizationWitness"
    assert anchor in text

    block = text.split(anchor, 1)[1].split(
        "/--\nFinite-dimensional regularization witness:", 1
    )[0]
    assert "bridge_fluid_helicity_of_canonicalDrazinProductionWitness" in block
    assert "{ canonicalRegularization := hCanon, helicity := hHelicity }" in block


def test_master_synthesis_canonical_drazin_regularization_wrapper_routes_through_packet_bridge() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = "private theorem bits_to_gravity_to_fluid_capstone_of_canonicalDrazinRegularizationWitness"
    assert anchor in text

    block = text.split(anchor, 1)[1].split(
        "/--\nCanonical-Drazin witness route with a proof-carrying ZPE gravity packet.", 1
    )[0]
    assert "bits_to_gravity_to_fluid_capstone_of_canonicalDrazinFluidHelicityWitness" in block
    assert "hFluidHelicity := { canonicalRegularization := hCanon, helicity := hHelicity }" in block
    assert "(h_mp := hCanon.h_mp)" not in block
    assert "(h_dr_star_canonical := hCanon.h_star_canonical)" not in block
