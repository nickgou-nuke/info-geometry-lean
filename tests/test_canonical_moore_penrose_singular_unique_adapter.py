from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
CANON = REPO / "lean" / "InfoGeometry" / "Canonical" / "MoorePenrose.lean"
SING = REPO / "lean" / "InfoGeometry" / "Singular" / "MoorePenrose.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    pattern = rf"(?m)^\s*(?:@[^[\n]+\]\s*)*(?:private\s+)?{kind}\s+{re.escape(name)}(?:\s|:|\().*$"
    match = re.search(pattern, text)
    assert match, f"missing {kind} {name}"
    start = match.start()
    line_end = text.find("\n", match.end())
    search_from = line_end + 1 if line_end != -1 else match.end()
    next_decl = re.search(
        r"(?m)^\s*(?:/-!|section|end|namespace|@[^[\n]+\]\s*)*"
        r"(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+",
        text[search_from:],
    )
    end = search_from + next_decl.start() if next_decl else len(text)
    return text[start:end]


def test_singular_moore_penrose_unique_root_exists():
    text = SING.read_text()
    assert "theorem MoorePenrose_unique" in text
    block = decl_block(text, "theorem", "MoorePenrose_unique")
    assert "hB.ab_adj_eq" in block
    assert "hC.ab_adj_eq" in block
    assert "hB.aba_eq_a" in block
    assert "hC.bab_eq_b" in block


def test_canonical_moore_penrose_unique_is_singular_adapter():
    text = CANON.read_text()
    assert "import InfoGeometry.Singular.MoorePenrose" in text
    assert "private theorem toSingular" in text
    block = decl_block(text, "theorem", "unique")
    assert "InfoGeometry.Singular.MoorePenrose.MoorePenrose_unique" in block
    assert "toSingular hB" in block
    assert "toSingular hC" in block
    assert "have h1 : a * b = a * c" not in block
    assert "star_mul_triple" not in block
