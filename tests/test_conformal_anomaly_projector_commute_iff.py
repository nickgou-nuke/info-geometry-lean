from pathlib import Path
import re
import unittest


REPO = Path(__file__).resolve().parents[1]
TARGET = REPO / "lean" / "InfoGeometry" / "Canonical" / "ConformalAnomalySource.lean"


def has_decl(text: str, kind: str, name: str) -> bool:
    return re.search(rf"\b{kind}\s+{re.escape(name)}\b", text) is not None


class ConformalAnomalyProjectorCommuteIffTests(unittest.TestCase):
    def test_chiral_scale_zero_iff_commute_surface_exists(self) -> None:
        text = TARGET.read_text()
        self.assertTrue(
            has_decl(text, "theorem", "chiralScale_eq_zero_iff_projectors_commute")
        )
        self.assertIn("CI.projectorObstruction_eq_zero_iff_commute", text)
        self.assertIn("CI.chiralScale_eq_projectorObstruction_nnnorm", text)


if __name__ == "__main__":
    unittest.main()
