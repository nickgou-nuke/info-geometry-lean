from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
OWNER = REPO / "lean" / "InfoGeometry" / "Quantum" / "Fierz.lean"
CONSUMER = REPO / "lean" / "InfoGeometry" / "Canonical" / "FierzReadout.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    match = re.search(
        rf"(?ms)^\s*{kind}\s+{re.escape(name)}(?:\s|\().*?(?=^\s*(?:omit \[[^\n]+\] in\n)?(?:/--.*?-/\s*)?(?:@[^[\n]+\n\s*)*(?:theorem|lemma|def|namespace|section|end|/-!)\b|\Z)",
        text,
    )
    assert match, f"missing {kind} {name}"
    return match.group(0)


def test_info_area_owner_root_names_cauchy_schwarz_bound() -> None:
    text = OWNER.read_text(encoding="utf-8")
    root = decl_block(text, "lemma", "infoArea_cauchy_schwarz_bound")
    assert "real_inner_mul_inner_self_le" in root
    assert "WithLp.fst ψ" in root
    assert "WithLp.snd ψ" in root
    nonneg = decl_block(text, "theorem", "infoArea_nonneg")
    assert "infoArea_cauchy_schwarz_bound" in nonneg
    assert "real_inner_mul_inner_self_le" not in nonneg


def test_doubled_fierz_area_consumer_uses_owner_area_nonneg() -> None:
    text = CONSUMER.read_text(encoding="utf-8")
    block = decl_block(text, "theorem", "doubledFierzReadout_area_nonneg")
    assert "infoArea_nonneg" in block
    assert "infoArea_cauchy_schwarz_bound" not in block
