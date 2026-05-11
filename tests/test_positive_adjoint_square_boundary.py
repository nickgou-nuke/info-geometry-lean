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
    assert "import Mathlib.Analysis.InnerProductSpace.Adjoint" in text
    assert "import Mathlib.Analysis.InnerProductSpace.Projection.Submodule" in text
    assert "import Mathlib.Analysis.InnerProductSpace.Positive" not in text


def test_adjoint_comp_self_positive_routes_to_mathlib_root():
    text = SINGULAR.read_text()
    block = decl_block(text, "theorem", "exists_moorePenroseInverse_global")
    assert "(A : E →L[ℝ] E)" in block
    assert "∃ (B : E →L[ℝ] E), IsMoorePenroseInverse A B" in block
    header = block.split(":=", 1)[0]
    assert "[FiniteDimensional ℝ E]" in header
    assert "True" not in block
    assert "sorry" not in block
    assert "admit" not in block


def test_endomorphism_star_squares_are_positive_and_not_witness_packaged():
    text = SINGULAR.read_text()
    exists_mp = decl_block(text, "theorem", "exists_moorePenroseInverse_endomorphism_of_isUnit")
    exists_dr = decl_block(text, "theorem", "exists_drazinInverse_endomorphism_of_isUnit")

    assert "[FiniteDimensional ℝ E]" in exists_mp.split(":=", 1)[0]
    assert "[FiniteDimensional ℝ E]" in exists_dr.split(":=", 1)[0]
    assert "exists_moorePenroseInverse_of_isUnit" in exists_mp
    assert "exists_drazinInverse_of_isUnit" in exists_dr

    for block in (exists_mp, exists_dr):
        assert "Witness" not in block
        assert "certificate" not in block.lower()
        assert "obligation" not in block.lower()
        assert "True" not in block
        assert "sorry" not in block
        assert "admit" not in block
