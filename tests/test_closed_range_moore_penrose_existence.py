from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
SINGULAR = REPO / "lean" / "InfoGeometry" / "Canonical" / "Singular.lean"
CIK = REPO / "lean" / "InfoGeometry" / "Canonical" / "CertifiedInverseKernel.lean"


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


def test_closed_range_mp_existence_uses_restricted_inverse_not_finite_dimension():
    text = SINGULAR.read_text()
    block = decl_block(text, "theorem", "exists_moorePenroseInverse_of_closedRange_with_projectors")
    header = block.split(":=", 1)[0]
    assert "hClosedRange : IsClosed (A.range : Set E)" in header
    assert "FiniteDimensional" not in header
    assert "let K : Submodule ℝ E := A.kerᗮ" in block
    assert "let R : Submodule ℝ E := A.range" in block
    assert "hClosedRange.completeSpace_coe" in block
    assert "ContinuousLinearEquiv.ofBijective AresCLM" in block
    assert "K.orthogonalProjection" in block
    assert "R.orthogonalProjection" in block


def test_closed_range_mp_existence_returns_penrose_and_projector_identities():
    text = SINGULAR.read_text()
    block = decl_block(text, "theorem", "exists_moorePenroseInverse_of_closedRange_with_projectors")
    assert "∃ (B : E →L[ℝ] E)" in block
    assert "IsMoorePenroseInverse A B" in block
    assert "A * B = A.range.starProjection" in block
    assert "B * A = A.kerᗮ.starProjection" in block
    assert "have hAB : A.comp B = R.starProjection" in block
    assert "have hBA : B.comp A = K.starProjection" in block
    assert "have haba : A * B * A = A" in block
    assert "have hbab : B * A * B = B" in block
    assert "have habstar : star (A * B) = A * B" in block
    assert "have hbastar : star (B * A) = B * A" in block


def test_cik_closed_range_readbacks_use_closed_range_existence_and_uniqueness():
    text = CIK.read_text()
    mp = decl_block(text, "theorem", "mpRangeProjector_eq_range_starProjection_of_closedRange")
    assert "hClosedRange : IsClosed (CIK.A.range : Set E)" in mp
    assert "exists_moorePenroseInverse_of_closedRange_with_projectors" in mp
    assert "IsMoorePenroseInverse.unique CIK.hMoorePenrose hB" in mp
    assert "hAB" in mp
    assert "hAD" not in mp.split(":=", 1)[0]

    metric = decl_block(text, "theorem", "metricProjector_eq_kerOrthogonal_starProjection_of_closedRange")
    assert "hClosedRange : IsClosed (CIK.A.range : Set E)" in metric
    assert "exists_moorePenroseInverse_of_closedRange_with_projectors" in metric
    assert "IsMoorePenroseInverse.unique CIK.hMoorePenrose hB" in metric
    assert "hBA" in metric
    assert "hAD" not in metric.split(":=", 1)[0]
