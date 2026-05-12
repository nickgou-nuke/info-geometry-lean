from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "ModularCartanCantorSystem.lean"


def test_modular_cartan_cantor_system_surface_exists() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "def modularTwin" in text
    assert "theorem modularTwin_modularTwin_of_involutive" in text
    assert "def pairTheta" in text
    assert "theorem pairTheta_pairTheta_of_involutive" in text
    assert "def selfDualTwinPair" in text
    assert "def antiSelfDualTwinPair" in text
    assert "theorem modularTwin_preserves_cylinder_split" in text
    assert "def cylinderLogIncrement" in text
    assert "theorem cylinderLogIncrement_common_pos_smul" in text
    assert "theorem relativeCountModularProfile_projective_rescale" in text


def test_modular_cartan_cantor_system_does_not_claim_trace_or_type_iii_barrier() -> None:
    text = FILE.read_text(encoding="utf-8")

    forbidden = [
        "FiniteDimensional",
        "Matrix.det",
        "logDet",
        "traceClass",
        "Tr(",
        "HasTrace",
        "TypeIII",
        "J M J",
        "self-concordant",
    ]

    for token in forbidden:
        assert token not in text
