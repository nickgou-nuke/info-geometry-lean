import re
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
VANDERMONDE = REPO / "lean" / "InfoGeometry" / "Canonical" / "VandermondeExclusionBridge.lean"
WEYL_D4 = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylCharacterVandermondeShadow.lean"
TWO_NODE = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylTwoNodeCancellationChart.lean"
A2 = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylA2CancellationChart.lean"


def live_decl(text: str, kind: str, name: str) -> bool:
    return bool(re.search(rf"(?m)^\s*(?:@[^[\n]+\n\s*)*{kind}\s+{re.escape(name)}\b", text))


def test_vandermonde_root_chain_is_mathlib_rooted_data_not_witness_packaging() -> None:
    text = VANDERMONDE.read_text(encoding="utf-8")
    assert live_decl(text, "structure", "FiniteVandermondeExclusionData")
    assert "FiniteVandermondeExclusionWitness" not in text
    assert "Matrix.det_vandermonde W.nodes" in text
    assert "Matrix.det_vandermonde_eq_zero_iff" in text
    assert "Matrix.det_vandermonde_ne_zero_iff" in text
    assert live_decl(text, "theorem", "determinant_eq_pairwise_separation")
    assert live_decl(text, "theorem", "determinant_eq_zero_iff_collision")
    assert live_decl(text, "theorem", "determinant_ne_zero_iff_injective")
    assert live_decl(text, "theorem", "collision_forces_determinant_zero")
    assert live_decl(text, "theorem", "determinant_ne_zero_forbids_collision")


def test_vandermonde_consumers_use_data_names_not_witness_names() -> None:
    for path in [WEYL_D4, TWO_NODE, A2]:
        text = path.read_text(encoding="utf-8")
        assert "FiniteVandermondeExclusionWitness" not in text
        assert "denominatorWitness" not in text
    assert "denominatorData : DenominatorShadow ℝ 4" in WEYL_D4.read_text(encoding="utf-8")
    assert "def denominatorData : FiniteVandermondeExclusionData" in TWO_NODE.read_text(encoding="utf-8")
    assert "def denominatorData : FiniteVandermondeExclusionData" in A2.read_text(encoding="utf-8")
