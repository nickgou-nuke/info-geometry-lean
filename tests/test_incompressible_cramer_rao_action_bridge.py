from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "IncompressibleCramerRaoActionBridge.lean"
BIT_SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "IncompressibleBitBridge.lean"
ALL = REPO / "lean" / "InfoGeometry" / "Canonical" / "All.lean"


def test_incompressible_cramer_rao_action_bridge_surface():
    text = SOURCE.read_text()

    assert "noncomputable abbrev souriauFisherMetricOperator" in text
    assert "noncomputable def souriauFisherMetricVolumeShadow" in text
    assert "noncomputable def souriauFisherMetricVolumePotential" in text
    assert "structure CramerRaoNegLogVolumeAnomalyReadout" in text
    assert "chiralScale_eq_metricVolumePotential" in text
    assert "theorem unitOfAction_eq_metricVolumePotential" in text
    assert "theorem epsilon_eq_metricVolumePotential" in text
    assert "theorem anomalyReadoutPacket_eq_metricVolumePotential" in text
    assert "-Real.log (souriauFisherMetricVolumeShadow H x)" in text
    assert "theorem chiralScale_eq_zero_of_incompressible" in text
    assert "theorem normalInference_of_incompressible" in text
    assert "theorem unitOfAction_eq_zero_of_incompressible" in text
    assert (
        "theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible"
        in text
    )
    assert "theorem semanticCollapsePacket_of_incompressible" in text
    assert "IncompressibleMongeAmpere" in text
    assert "IncompressibleCramerRaoBit" in text
    assert "incompressibleCramerRaoBit_of_incompressible" in text
    assert "isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume" in text
    assert "CramerRaoLogVolumeAnomalyReadout" not in text
    assert "chiralScale_eq_logAbsDet" not in text


def test_incompressible_bit_bridge_surface():
    text = BIT_SOURCE.read_text()

    assert "def UnitRelativeVolumeBit" in text
    assert "def IncompressibleCramerRaoBit" in text
    assert "theorem incompressibleCramerRaoBit_of_incompressible" in text
    assert "theorem logAbsDet_cramerRaoMetric_eq_zero_of_incompressibleBit" in text
    assert "theorem isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume" in text
    assert "theorem unitOfAction_eq_zero_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume" in text


def test_incompressible_cramer_rao_action_bridge_operatorial_redline():
    text = SOURCE.read_text()

    assert "The metric is the primary operatorial datum" in text
    assert "not replacements for it" in text
    assert "Berezinian/super-Berezinian" in text
    assert "dilation/Goldstone channel is not a new scalar charge" in text
    assert "CI.P_D * CI.D - CI.D * CI.P_D = 0" in text
    assert "ConformalInference.semanticCollapsePacket" in text


def test_incompressible_cramer_rao_action_bridge_imported_by_all():
    text = ALL.read_text()

    assert "import InfoGeometry.Canonical.IncompressibleBitBridge" in text
    assert "import InfoGeometry.Canonical.IncompressibleCramerRaoActionBridge" in text
