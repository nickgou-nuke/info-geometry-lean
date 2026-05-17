from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauLieThermoKKTBridge.lean"


def test_exact_kkt_context_removes_explicit_stationarity_packet_field() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    struct_anchor = (
        "structure ExactKKTResidualSouriauLieThermoKKTContext [Fintype α] [Nonempty α] where"
    )
    assert struct_anchor in text
    struct_block = text.split(struct_anchor, 1)[1].split(
        "namespace ExactKKTResidualSouriauLieThermoKKTContext", 1
    )[0]
    assert "kktStationarity : KKTEntropyStationarityShadow" not in struct_block

    assert (
        "def toSouriauLieThermoKKTContext"
        in text
    )
    adapter_block = text.split("def toSouriauLieThermoKKTContext", 1)[1].split(
        "/-! ## Finite Souriau/Fenchel/Onsager projections -/", 1
    )[0]
    assert (
        "kktStationarity :=\n"
        "      DimensionAgnosticKKTResiduals.toShadow DimensionAgnosticKKTResiduals.exact"
        in adapter_block
    )
    assert "theorem kktStationarity_packet" in adapter_block
    assert "KKTEntropyStationarityShadow.mk_exact" in adapter_block
