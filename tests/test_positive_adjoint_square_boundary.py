from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
SINGULAR = REPO / "lean" / "InfoGeometry" / "Canonical" / "Singular.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    pattern = rf"(?m)^\s*(?:@[^[\n]+\]\s*)*(?:noncomputable\s+)?{kind}\s+{re.escape(name)}(?:\s|:|\().*$"
    match = re.search(pattern, text)
    assert match, f"missing {kind} {name}"
    start = match.start()
    line_end = text.find("\n", match.end())
    search_from = line_end + 1 if line_end != -1 else match.end()
    nxt = re.search(
        r"(?m)^\s*(?:/-!|section|end|namespace|@[^[\n]+\]\s*)*"
        r"(?:noncomputable\s+)?(?:lemma|theorem|def|abbrev)\s+",
        text[search_from:],
    )
    end = search_from + nxt.start() if nxt else len(text)
    return text[start:end]


def test_positive_adjoint_square_imports_mathlib_positive_operator_api():
    text = SINGULAR.read_text()
    assert "import Mathlib.Analysis.InnerProductSpace.Positive" in text


def test_adjoint_comp_self_positive_routes_to_mathlib_root():
    text = SINGULAR.read_text()
    block = decl_block(text, "theorem", "adjoint_comp_self_isPositive")
    assert "(S† ∘L S).IsPositive" in block
    assert "ContinuousLinearMap.isPositive_adjoint_comp_self S" in block
    header = block.split(":=", 1)[0]
    assert "IsPositive" in header
    assert "True" not in block
    assert "sorry" not in block
    assert "admit" not in block


def test_endomorphism_star_squares_are_positive_and_not_witness_packaged():
    text = SINGULAR.read_text()
    star_left = decl_block(text, "theorem", "star_mul_self_isPositive")
    star_right = decl_block(text, "theorem", "mul_star_self_isPositive")

    assert "(star A * A).IsPositive" in star_left
    assert "ContinuousLinearMap.isPositive_adjoint_comp_self A" in star_left
    assert "star_eq_adjoint" in star_left
    assert "ContinuousLinearMap.mul_def" in star_left

    assert "(A * star A).IsPositive" in star_right
    assert "ContinuousLinearMap.isPositive_self_comp_adjoint A" in star_right
    assert "star_eq_adjoint" in star_right
    assert "ContinuousLinearMap.mul_def" in star_right

    for block in (star_left, star_right):
        assert "Witness" not in block
        assert "certificate" not in block.lower()
        assert "obligation" not in block.lower()
        assert "True" not in block
        assert "sorry" not in block
        assert "admit" not in block
