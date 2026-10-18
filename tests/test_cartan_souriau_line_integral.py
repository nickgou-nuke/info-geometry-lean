from pathlib import Path
import re


def test_massieu_directional_line_integral_theorem_is_live():
    source = (
        Path(__file__).parents[1]
        / "lean/InfoGeometry/Algebraic/CartanSouriauMassieuDirectionalCalculus.lean"
    ).read_text()
    assert re.search(
        r"(?m)^theorem\s+massieu_directional_line_integral_eq_endpoint_difference\b",
        source,
    )
