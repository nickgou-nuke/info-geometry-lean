import re
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
FIERZ_READOUT = REPO / "lean" / "InfoGeometry" / "Canonical" / "FierzReadout.lean"
FIERZ_DERIVATION = (
    REPO / "lean" / "InfoGeometry" / "Canonical" / "OperatorialFierzDerivationBridge.lean"
)
QUANTUM_FIERZ = REPO / "lean" / "InfoGeometry" / "Quantum" / "Fierz.lean"


def live_decl(text: str, kind: str, name: str) -> bool:
    return bool(re.search(rf"(?m)^\s*(?:@[^[\n]+\n\s*)*{kind}\s+{re.escape(name)}\b", text))


def test_fierz_readout_separates_projection_from_full_fierz_presentation() -> None:
    text = FIERZ_READOUT.read_text(encoding="utf-8")

    assert live_decl(text, "structure", "FierzPresentation")
    assert live_decl(text, "def", "toFierzPresentationWith")
    assert live_decl(text, "def", "ofFierzPresentation")
    assert live_decl(text, "theorem", "of_toFierzPresentationWith")
    assert live_decl(text, "theorem", "toFierzPresentationWith_ofFierzPresentation")

    assert "projection forgetting `scalarReadout` and `areaReadout`" in text
    assert "scalar and area channels remain in the original" in text
    assert "doubledFierzReadout_isMajoranaShadow_iff" in text
    assert "infoHilbert_nonneg" in text
    assert "infoArea_nonneg" in text


def test_quantum_fierz_owner_roots_are_used_for_support_and_majorana_shadow() -> None:
    text = QUANTUM_FIERZ.read_text(encoding="utf-8")
    assert live_decl(text, "theorem", "infoHilbert_nonneg")
    assert live_decl(text, "theorem", "infoArea_nonneg")
    assert live_decl(text, "theorem", "information_fierz_identity")
    assert live_decl(text, "theorem", "information_fierz_majorana")


def test_operatorial_fierz_derivation_is_not_named_as_spacetime_equivalence() -> None:
    text = FIERZ_DERIVATION.read_text(encoding="utf-8")
    forbidden = [
        "Thermodynamic Gravity Equivalence",
        "Spacetime exists",
        "emergentSpacetimeDerivation",
        "SpacetimeIsThermalFlow",
        "emergentSpacetime_is_derivation",
    ]
    for phrase in forbidden:
        assert phrase not in text

    assert live_decl(text, "def", "fierzGrade1InnerDerivation")
    assert live_decl(text, "def", "ModularFlowMatchesFierzGrade1Derivation")
    assert live_decl(text, "theorem", "fierzGrade1InnerDerivation_leibniz")
    assert "derivation matching predicate" in text
