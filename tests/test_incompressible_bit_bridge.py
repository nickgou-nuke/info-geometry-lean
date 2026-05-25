from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
BRIDGE = REPO / "lean" / "InfoGeometry" / "Canonical" / "IncompressibleBitBridge.lean"
ALL = REPO / "lean" / "InfoGeometry" / "Canonical" / "All.lean"


def test_incompressible_bit_bridge_exposes_relative_volume_and_cramer_rao_bits() -> None:
    text = BRIDGE.read_text(encoding="utf-8")

    assert "structure UnitRelativeVolumeBit" in text
    assert "relativeVolumeChangeRN n M = 1" in text
    assert "theorem kahlerPotentialRN_eq_zero_of_unitRelativeVolumeBit" in text
    assert "theorem chiralScale_eq_zero_of_unitRelativeVolumeBit" in text
    assert "bit.unit_relative_volume" in text
    assert "theorem unitOfAction_eq_zero_of_unitRelativeVolumeBit" in text
    assert "structure IncompressibleCramerRaoBit" in text
    assert "theorem logAbsDet_cramerRaoMetric_eq_zero_of_incompressibleBit" in text


def test_anomaly_scale_uses_negative_cramer_rao_log_volume_redline() -> None:
    text = BRIDGE.read_text(encoding="utf-8")

    assert (
        "theorem isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume"
        in text
    )
    assert (
        "theorem unitOfAction_eq_zero_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume"
        in text
    )
    assert "hScaleFromNegLogVolume" in text
    assert "CI.chiralScale =" in text
    assert "-Real.log (|LinearMap.det (cramerRaoMetricOp H x).toLinearMap|)" in text
    assert "CI.unitOfAction_eq_zero_of_normalInference hNormal" in text
    assert "chiralScale_eq_cramerRaoLogVolume" not in text


def test_incompressible_bit_bridge_is_wired_into_canonical_umbrella() -> None:
    text = ALL.read_text(encoding="utf-8")

    assert "import InfoGeometry.Canonical.IncompressibleBitBridge" in text
