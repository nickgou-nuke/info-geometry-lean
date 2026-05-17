from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def test_master_synthesis_exposes_certified_inverse_kernel_production_witness_route() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    anchor = (
        "private theorem "
        "bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_"
        "of_productionWitness_of_zpeGravityWitness_and_thermalBottWitness"
    )
    assert anchor in text
    signature, body_tail = text.split(anchor, 1)[1].split(
        "\n  bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_ownerWitnesses", 1
    )
    body = "bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_ownerWitnesses" + body_tail.split(
        "/--\nRegularization-sourced capstone wrapper:", 1
    )[0]

    assert "(hZPEGravity : ZPEGravityWitness (E := E) S c R Kgeo x)" in signature
    assert "(Wfluid : FluidHelicityProductionWitness (E := E) A B_mp B_dr)" in signature
    assert "(hThermalBott : ThermalBottWitness (E := E))" in signature
    assert "(hRankPos : 0 < Module.finrank ℝ E)" not in signature
    assert "(hEin : IsEinsteinKaehlerAtWith c R Kgeo x)" not in signature
    assert "(hAnomalySkew :" not in signature
    assert "(hHelicity : MatchedHelicityWitness" not in signature
    assert "(Mod : ModularRadonNikodymData E)" not in signature
    assert "(V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))" not in signature
    assert "(IST : InfoSpectralTriple H₂)" not in signature
    assert "(hCompat : InformationalLichnerowiczBottCompatibility" not in signature
    assert "bits_to_gravity_to_fluid_capstone_of_certifiedInverseKernel_ownerWitnesses" in body
    assert "Wfluid.regularization" in body
    assert "Wfluid.helicity" in body
    assert "hThermalBott := hThermalBott" in body
