from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
CANON = REPO / "lean" / "InfoGeometry" / "Canonical" / "Drazin.lean"
SING = REPO / "lean" / "InfoGeometry" / "Singular" / "Drazin.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    pat = rf"(?m)^\s*(?:@[^[\n]+\]\s*)*(?:private\s+)?{kind}\s+{re.escape(name)}(?:\s|:|\().*$"
    starts = list(re.finditer(pat, text))
    assert starts, f"missing {kind} {name}"
    start = starts[0].start()
    line_end = text.find("\n", starts[0].end())
    search_from = line_end + 1 if line_end != -1 else starts[0].end()
    nxt = re.search(
        r"(?m)^\s*(?:/-!|section|end|namespace|@[^[\n]+\]\s*)*(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+",
        text[search_from:],
    )
    end = search_from + nxt.start() if nxt else len(text)
    return text[start:end]


def test_singular_drazin_star_roots_exist():
    text = SING.read_text()
    assert "theorem star_isDrazinInverse" in text
    assert "theorem Drazin_star_eq_self_of_selfAdjoint" in text
    root = decl_block(text, "theorem", "Drazin_star_eq_self_of_selfAdjoint")
    assert "star_isDrazinInverse" in root
    assert "Drazin_unique" in root


def test_canonical_star_transport_is_adapter_over_singular_root():
    text = CANON.read_text()
    assert "private theorem fromSingular" in text
    block = decl_block(text, "theorem", "star_isDrazinInverse")
    assert "InfoGeometry.Singular.Drazin.IsDrazinInverse.star_isDrazinInverse" in block
    assert "fromSingular" in block
    assert "congrArg star h.comm" not in block
    assert "congrArg star h.power" not in block


def test_canonical_selfadjoint_star_uses_singular_selfadjoint_root():
    text = CANON.read_text()
    block = decl_block(text, "theorem", "star_eq_self_of_selfAdjoint")
    assert "InfoGeometry.Singular.Drazin.Drazin_star_eq_self_of_selfAdjoint" in block
    assert "toSingular h" in block
    assert "star_isDrazinInverse_of_selfAdjoint" not in block
