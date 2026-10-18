from pathlib import Path
import re


def test_finite_entropy_change_counterexample_is_live():
    source = (
        Path(__file__).parents[1]
        / "lean/InfoGeometry/Algebraic/CartanExponentialFamily.lean"
    ).read_text()
    assert re.search(
        r"(?m)^theorem\s+boltzmannEntropy_delta_ne_massieu_delta_fin_two\b",
        source,
    )
