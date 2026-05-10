from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
CIK = REPO / "lean" / "InfoGeometry" / "Canonical" / "CertifiedInverseKernel.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    pattern = rf"(?m)^\s*(?:@[^[\n]+\]\s*)*(?:noncomputable\s+)?{kind}\s+{re.escape(name)}(?:\s|:|\().*$"
    match = re.search(pattern, text)
    assert match, f"missing {kind} {name}"
    start = match.start()
    line_end = text.find("\n", match.end())
    search_from = line_end + 1 if line_end != -1 else match.end()
    next_decl = re.search(
        r"(?m)^\s*(?:/-!|section|end|namespace|@[^[\n]+\]\s*)*"
        r"(?:noncomputable\s+)?(?:lemma|theorem|def|abbrev)\s+",
        text[search_from:],
    )
    end = search_from + next_decl.start() if next_decl else len(text)
    return text[start:end]


def test_of_selfadjoint_idempotent_constructor_uses_real_roots():
    text = CIK.read_text()
    block = decl_block(text, "def", "ofSelfAdjointIdempotent")
    assert "A := P" in block
    assert "A_D := P" in block
    assert "A_MP := P" in block
    assert "drazinIndex := 1" in block
    assert "IsDrazinInverse.of_idempotent hIdem" in block
    assert "IsMoorePenroseInverse.mk" in block
    assert "hStar" in block


def test_of_selfadjoint_idempotent_exposes_base_selfadjoint_hA():
    text = CIK.read_text()
    block = decl_block(text, "theorem", "ofSelfAdjointIdempotent_A_selfAdjoint")
    assert "hStar" in block
    assert "star" in block
    assert "ofSelfAdjointIdempotent" in block


def test_of_selfadjoint_idempotent_derives_had_from_hA_path():
    text = CIK.read_text()
    block = decl_block(text, "theorem", "ofSelfAdjointIdempotent_A_D_star")
    assert "A_D_star_of_selfAdjoint" in block
    assert "ofSelfAdjointIdempotent_A_selfAdjoint" in block
    assert "hAD" not in block.split(":=", 1)[0]


def test_of_selfadjoint_idempotent_projector_star_uses_hA_only():
    text = CIK.read_text()
    block = decl_block(text, "theorem", "ofSelfAdjointIdempotent_spectralProjector_star")
    assert "spectralProjector_star_of_A_selfAdjoint" in block
    assert "ofSelfAdjointIdempotent_A_selfAdjoint" in block
    assert "hAD" not in block.split(":=", 1)[0]
