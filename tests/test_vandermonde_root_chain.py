import re
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
VANDERMONDE = REPO / "lean" / "InfoGeometry" / "Canonical" / "VandermondeExclusionBridge.lean"
WEYL_D4 = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylCharacterVandermondeShadow.lean"
TWO_NODE = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylTwoNodeCancellationChart.lean"
A2 = REPO / "lean" / "InfoGeometry" / "Canonical" / "WeylA2CancellationChart.lean"


def live_decl(text: str, kind: str, name: str) -> bool:
    return bool(re.search(rf"(?m)^\s*(?:@[^[\n]+\n\s*)*{kind}\s+{re.escape(name)}\b", text))


def test_vandermonde_root_chain_is_mathlib_rooted_witness_surface() -> None:
    text = VANDERMONDE.read_text(encoding="utf-8")
    assert live_decl(text, "structure", "FiniteVandermondeExclusionWitness")
    assert "FiniteVandermondeExclusionData" not in text
    assert "Matrix.det_vandermonde W.nodes" in text
    assert "Matrix.det_vandermonde_eq_zero_iff" in text
    assert "Matrix.det_vandermonde_ne_zero_iff" in text
    assert live_decl(text, "theorem", "determinant_eq_pairwise_separation")
    assert live_decl(text, "theorem", "determinant_eq_zero_iff_collision")
    assert live_decl(text, "theorem", "determinant_ne_zero_iff_injective")
    assert live_decl(text, "theorem", "collision_forces_determinant_zero")
    assert live_decl(text, "theorem", "determinant_ne_zero_forbids_collision")


def test_vandermonde_consumers_use_current_witness_names() -> None:
    d4_text = WEYL_D4.read_text(encoding="utf-8")
    two_node_text = TWO_NODE.read_text(encoding="utf-8")
    a2_text = A2.read_text(encoding="utf-8")

    assert "FiniteVandermondeExclusionWitness" in d4_text
    assert "denominatorWitness" in d4_text
    assert "abbrev DenominatorShadow" in d4_text

    assert "def denominatorWitness : FiniteVandermondeExclusionWitness" in two_node_text
    assert "def denominatorWitness : FiniteVandermondeExclusionWitness" in a2_text
    assert "denominator_eq_zero_iff" in two_node_text
    assert "denominator_eq_zero_iff_collision" in a2_text
