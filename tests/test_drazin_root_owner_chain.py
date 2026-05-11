from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
SINGULAR = REPO / "lean" / "InfoGeometry" / "Singular" / "Drazin.lean"
CANONICAL = REPO / "lean" / "InfoGeometry" / "Canonical" / "Drazin.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    match = re.search(
        rf"(?ms)^\s*(?:/--.*?-/[\n\s]*)?(?:@[^[\n]+\n\s*)*{kind}\s+{re.escape(name)}(?:\s|\().*?(?=^\s*(?:/--.*?-/\s*)?(?:@[^[\n]+\n\s*)*(?:theorem|lemma|def|namespace|section|end)\b|\Z)",
        text,
    )
    assert match, f"missing {kind} {name}"
    return match.group(0)


def test_singular_drazin_projector_idempotent_has_root_calculation() -> None:
    text = SINGULAR.read_text(encoding="utf-8")
    root = decl_block(text, "lemma", "drazin_projector_idempotent'")
    assert "D * A * D" in root
    assert "h.dad_eq_d" in root
    top = decl_block(text, "lemma", "Drazin_Projector_idempotent")
    assert "calc" in top
    assert "h.dad_eq_d" in top


def test_canonical_projection_idempotent_matches_current_direct_calc() -> None:
    text = CANONICAL.read_text(encoding="utf-8")
    block = decl_block(text, "theorem", "projection_is_idempotent")
    assert "calc" in block
    assert "noncomm_ring" in block
    assert "h.idempotent" in block
    assert "InfoGeometry.Singular.Drazin.Drazin_Projector_idempotent" not in block
