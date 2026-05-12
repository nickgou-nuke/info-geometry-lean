from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "BogoliubovCartanEigenOperator.lean"


def test_bogoliubov_cartan_eigen_operator_exports_exist() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "def cartanAdjoint" in text
    assert "def IsCartanEigenOperator" in text
    assert "theorem cartanAdjoint_add" in text
    assert "theorem cartanAdjoint_smul" in text
    assert "theorem cartanEigenOperator_conjugate" in text
