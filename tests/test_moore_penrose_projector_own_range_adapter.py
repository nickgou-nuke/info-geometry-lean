from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
MP = REPO / "lean" / "InfoGeometry" / "Canonical" / "MoorePenrose.lean"
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


def test_canonical_mp_projectors_have_generic_own_range_starprojection_readbacks():
    text = MP.read_text()
    right = decl_block(text, "theorem", "rightProjector_eq_ownRange_starProjection")
    assert "rightProjector_isStarProjection h" in right
    assert "isStarProjection_iff_eq_starProjection_range.mp" in right
    assert "rightProjector A B" in right
    assert "range.starProjection" in right

    left = decl_block(text, "theorem", "leftProjector_eq_ownRange_starProjection")
    assert "leftProjector_isStarProjection h" in left
    assert "isStarProjection_iff_eq_starProjection_range.mp" in left
    assert "leftProjector A B" in left
    assert "range.starProjection" in left


def test_canonical_mp_projectors_expose_range_and_kernel_orthogonal_readbacks():
    text = MP.read_text()
    right_range = decl_block(text, "theorem", "rightProjector_range_eq_range")
    assert "h.aba_eq_a" in right_range
    assert "rightProjector A B" in right_range
    assert "A.range" in right_range

    right = decl_block(text, "theorem", "rightProjector_eq_range_starProjection")
    assert "rightProjector_range_eq_range h" in right
    assert "rightProjector_eq_ownRange_starProjection h" in right
    assert "A.range.starProjection" in right

    left_range = decl_block(text, "theorem", "leftProjector_range_eq_ker_orthogonal")
    assert "h.aba_eq_a" in left_range
    assert "leftProjector_eq_ownRange_starProjection h" in left_range
    assert "orthogonal_range" in left_range
    assert "A.kerᗮ" in left_range

    left = decl_block(text, "theorem", "leftProjector_eq_kerOrthogonal_starProjection")
    assert "leftProjector_range_eq_ker_orthogonal h" in left
    assert "leftProjector_eq_ownRange_starProjection h" in left
    assert "A.kerᗮ.starProjection" in left


def test_cik_own_range_readbacks_can_be_seen_as_consumers_of_generic_mp_adapters():
    text = CIK.read_text()
    mp = decl_block(text, "theorem", "mpRangeProjector_eq_ownRange_starProjection")
    metric = decl_block(text, "theorem", "metricProjector_eq_ownRange_starProjection")
    assert "mpRangeProjector_isStarProjection" in mp
    assert "isStarProjection_iff_eq_starProjection_range.mp" in mp
    assert "metricProjector_isStarProjection" in metric
    assert "isStarProjection_iff_eq_starProjection_range.mp" in metric
