from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
OWNER = REPO / "lean" / "InfoGeometry" / "Quantum" / "Fierz.lean"
CONSUMER = REPO / "lean" / "InfoGeometry" / "Canonical" / "FierzReadout.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    match = re.search(
        rf"(?ms)^\s*(?:noncomputable\s+)?{kind}\s+{re.escape(name)}(?:\s|\().*?(?=^\s*(?:omit \[[^\n]+\] in\n)?(?:/--.*?-/\s*)?(?:@[^[\n]+\n\s*)*(?:(?:noncomputable\s+)?(?:theorem|lemma|def)|namespace|section|end|/-!)\b|\Z)",
        text,
    )
    assert match, f"missing {kind} {name}"
    return match.group(0)


def test_info_area_owner_root_is_gram_determinant_and_feeds_fierz_identity() -> None:
    text = OWNER.read_text(encoding="utf-8")
    area = decl_block(text, "def", "infoArea")
    assert "inner ℝ (WithLp.fst ψ) (WithLp.fst ψ) * inner ℝ (WithLp.snd ψ) (WithLp.snd ψ)" in area
    assert "(inner ℝ (WithLp.fst ψ) (WithLp.snd ψ))^2" in area

    identity = decl_block(text, "theorem", "information_fierz_identity")
    assert "4 * (infoArea ψ)" in identity
    assert "unfold infoHilbert infoArea" in identity


def test_doubled_fierz_readout_area_channel_comes_from_owner_info_area() -> None:
    text = CONSUMER.read_text(encoding="utf-8")
    block = decl_block(text, "def", "doubledFierzReadout")
    assert "area := infoArea (E := E)" in block
    assert "fierzIdentity := information_fierz_identity (E := E)" in block
