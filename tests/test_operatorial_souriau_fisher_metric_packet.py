from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauLieThermoKKTBridge.lean"


def test_operatorial_souriau_fisher_metric_packet_surface():
    text = SOURCE.read_text()

    assert "theorem operatorialSouriauFisherMetric_packet_of_cramerRaoResponse" in text
    assert "comparisonStateGeneratorMetric" in text
    assert "operatorialFisherOnsager_eq_hessianReadout" in text
    assert "operatorialEntropyProduction_nonneg_of_cramerRaoResponse" in text
    assert "operatorCanonicalEntropyProduction_nonneg_of_cramerRaoResponse" in text
    assert "Operators.entropyProduction" in text
    assert "CramerRaoOperatorialResponseContext" in text
