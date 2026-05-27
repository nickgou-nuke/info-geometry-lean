from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauConformalKKTContext.lean"


def test_conformal_cartan_odd_tkk_cone_closure_route_exists() -> None:
    text = SOURCE.read_text(encoding="utf-8")

    assert "def toClosureContextOfTKKConeWitness" in text
    assert "theorem satisfiesKKT_TKK_Weyl_JordanLieClosure_of_TKKConeWitness" in text
    assert "(hTKK : ConformalTKKWitness (α := α) (H := H) C)" in text
    assert "(hCone : ConformalConeAdmissibilityWitness (α := α) (H := H) C)" in text
    assert "(W.toClosureContextOfTKKConeWitness weylGauge hTKK hCone X Y).SatisfiesKKT_TKK_Weyl_JordanLieClosure" in text
    assert "(W.toClosureContextOfTKKConeWitness weylGauge hTKK hCone X Y).satisfiesKKT_TKK_Weyl_JordanLieClosure" in text
