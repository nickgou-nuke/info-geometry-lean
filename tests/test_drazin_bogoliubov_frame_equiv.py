from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
FILE = REPO / "lean" / "InfoGeometry" / "Canonical" / "DrazinBogoliubovFrameEquiv.lean"


def test_drazin_bogoliubov_frame_equiv_exports_exist() -> None:
    text = FILE.read_text(encoding="utf-8")

    assert "def IsDrazinCartanEigenOperator" in text
    assert "def drazinProjection" in text
    assert "def drazinComplementaryProjection" in text
    assert "theorem drazinProjection_add_complementaryProjection" in text
    assert "theorem drazinProjection_is_idempotent_of_isDrazinCartanEigenOperator" in text
    assert "theorem drazinProjection_comm_self_of_isDrazinCartanEigenOperator" in text
    assert "theorem drazinProjection_conjugate_readback" in text
    assert "structure ChiralDrazinKreinPackage" in text
    assert "structure BogoliubovFrameOver" in text
    assert "def EquivalentBogoliubovFrames" in text
    assert "namespace EquivalentBogoliubovFrames" in text
    assert "theorem preserves_drazinProjection_comm" in text
    assert "theorem frame_action" in text
    assert "theorem projected_frame_readout_invariant" in text
    assert "theorem isDrazinInverse_of_isDrazinCartanEigenOperator" in text
    assert "theorem isCartanEigenOperator_of_isDrazinCartanEigenOperator" in text
    assert "theorem isDrazinCartanEigenOperator_conjugate" in text
