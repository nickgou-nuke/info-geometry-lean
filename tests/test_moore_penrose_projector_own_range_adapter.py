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
    right = decl_block(text, "theorem", "rightProjector_star")
    assert "star (rightProjector a b) = rightProjector a b" in right
    assert "h.ab_star" in right

    left = decl_block(text, "theorem", "leftProjector_star")
    assert "star (leftProjector a b) = leftProjector a b" in left
    assert "h.ba_star" in left


def test_canonical_mp_projectors_expose_range_and_kernel_orthogonal_readbacks():
    text = MP.read_text()
    right_range = decl_block(text, "theorem", "rightProjector_idempotent")
    assert "h.aba_eq_a" in right_range
    assert "rightProjector a b" in right_range

    left_range = decl_block(text, "theorem", "leftProjector_idempotent")
    assert "h.bab_eq_b" in left_range
    assert "leftProjector a b" in left_range


def test_cik_own_range_readbacks_can_be_seen_as_consumers_of_generic_mp_adapters():
    text = CIK.read_text()
    mp = decl_block(text, "theorem", "mpRangeProjector_star")
    metric = decl_block(text, "theorem", "metricProjector_star")
    assert "IsMoorePenroseInverse.rightProjector_star CIK.hMoorePenrose" in mp
    assert "IsMoorePenroseInverse.leftProjector_star CIK.hMoorePenrose" in metric
