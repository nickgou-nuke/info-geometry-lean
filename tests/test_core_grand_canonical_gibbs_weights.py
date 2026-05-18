from pathlib import Path


def test_core_grand_canonical_exports_two_param_gibbs_weight_bounds() -> None:
    text = Path("lean/InfoGeometry/Core/GrandCanonical.lean").read_text()

    assert "lemma gc2_gibbsWeight_nonneg" in text
    assert "lemma gc2_gibbsWeight_pos" in text
    assert "gibbsWeightGC_nonneg params β μ x" in text
    assert "gibbsWeightGC_pos params β μ x" in text
