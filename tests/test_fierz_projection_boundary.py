import re
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
FIERZ_READOUT = REPO / "lean" / "InfoGeometry" / "Canonical" / "FierzReadout.lean"
FIERZ_DERIVATION = (
    REPO / "lean" / "InfoGeometry" / "Canonical" / "OperatorialFierzDerivationBridge.lean"
)
QUANTUM_FIERZ = REPO / "lean" / "InfoGeometry" / "Quantum" / "Fierz.lean"


def live_decl(text: str, kind: str, name: str) -> bool:
    return bool(
        re.search(
            rf"(?m)^\s*(?:@[^[\n]+\n\s*)*(?:noncomputable\s+)?{kind}\s+{re.escape(name)}\b",
            text,
        )
    )


def test_fierz_readout_declares_readout_structure_and_projection_bridge() -> None:
    text = FIERZ_READOUT.read_text(encoding="utf-8")

    assert live_decl(text, "structure", "FierzChannelReadout")
    assert live_decl(text, "def", "toQuantumPresentationWith")
    assert live_decl(text, "def", "toQuantumPresentation")
    assert live_decl(text, "def", "defaultSupport")
    assert live_decl(text, "def", "defaultGenerator")
    assert live_decl(text, "theorem", "toQuantumPresentationWith_metricReadout")
    assert live_decl(text, "theorem", "toQuantumPresentationWith_phaseReadout")

    assert "This file does not introduce new Clifford owners." in text
    assert "Translator map from Fierz readout package to the generic presentation" in text


def test_quantum_fierz_owner_roots_cover_identity_and_majorana_specialization() -> None:
    text = QUANTUM_FIERZ.read_text(encoding="utf-8")
    assert live_decl(text, "def", "infoScalar")
    assert live_decl(text, "def", "infoSymplectic")
    assert live_decl(text, "def", "infoHilbert")
    assert live_decl(text, "def", "infoArea")
    assert live_decl(text, "theorem", "information_fierz_identity")
    assert live_decl(text, "def", "IsMajoranaBelief")
    assert live_decl(text, "theorem", "information_fierz_majorana")


def test_operatorial_fierz_derivation_uses_current_spacetime_equivalence_names() -> None:
    text = FIERZ_DERIVATION.read_text(encoding="utf-8")

    assert "Thermodynamic Gravity Equivalence" in text
    assert live_decl(text, "def", "emergentSpacetimeDerivation")
    assert live_decl(text, "def", "SpacetimeIsThermalFlow")
    assert live_decl(text, "theorem", "emergentSpacetime_is_derivation")
    assert "innerDerivation K_mod = emergentSpacetimeDerivation P Ψ Φ" in text
