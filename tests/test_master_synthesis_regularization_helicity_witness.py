from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
MASTER = REPO / "lean" / "InfoGeometry" / "Canonical" / "MasterSynthesis.lean"


def _theorem_block(text: str, name: str) -> str:
    anchor = f"private theorem {name}\n"
    start = text.index(anchor)
    next_candidates = [
        pos
        for pos in (
            text.find("\nprivate theorem ", start + 1),
            text.find("\nprivate def ", start + 1),
        )
        if pos != -1
    ]
    next_start = min(next_candidates) if next_candidates else len(text)
    return text[start:next_start]



def _declaration_head(block: str) -> str:
    return block.split("(N : ℕ) :", 1)[0]


def test_regularization_helicity_witness_capstone_exists() -> None:
    text = MASTER.read_text(encoding="utf-8")
    block = _theorem_block(text, "bits_to_gravity_to_fluid_capstone_of_regularizationWitness")
    head = _declaration_head(block)

    assert "(hReg : RegularizationWitness A B_dr)" in head
    assert "(hHelicity : HelicityPairingWitness A)" in head
    assert "(ω : VelocityField E →L[ℝ] ℝ)" not in head
    assert "(Ω : AlgebraEnd E →L[ℝ] ℝ)" not in head


def test_legacy_regularization_capstone_reroutes_through_witness_constructor() -> None:
    text = MASTER.read_text(encoding="utf-8")
    block = _theorem_block(text, "bits_to_gravity_to_fluid_capstone_of_regularization")

    assert "bits_to_gravity_to_fluid_capstone_of_regularizationWitness" in block
    assert "HelicityPairingWitness.of_eq" in block


def test_canonical_drazin_pairing_witness_capstone_exists() -> None:
    text = MASTER.read_text(encoding="utf-8")
    block = _theorem_block(
        text,
        "bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin_pairingWitness",
    )
    head = _declaration_head(block)

    assert "(hHelicity : HelicityPairingWitness A)" in head
    assert "(ω : VelocityField E →L[ℝ] ℝ)" not in head
    assert "(Ω : AlgebraEnd E →L[ℝ] ℝ)" not in head
    assert "bits_to_gravity_to_fluid_capstone_of_regularizationWitness" in block



def test_legacy_canonical_drazin_capstone_reroutes_through_pairing_witness() -> None:
    text = MASTER.read_text(encoding="utf-8")
    block = _theorem_block(
        text,
        "bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin",
    )

    assert (
        "bits_to_gravity_to_fluid_capstone_of_regularization_canonical_drazin_pairingWitness"
        in block
    )
    assert "HelicityPairingWitness.of_eq A ω Ω hHelicity" in block
