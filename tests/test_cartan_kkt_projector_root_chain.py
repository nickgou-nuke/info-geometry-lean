from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
OWNER = REPO / "lean" / "InfoGeometry" / "Cartan" / "Involution.lean"
CONSUMER = REPO / "lean" / "InfoGeometry" / "Canonical" / "KKTCore.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    starts = list(re.finditer(rf"(?m)^.*\b{kind}\s+{re.escape(name)}(?:\s|:|\().*$", text))
    assert starts, f"missing {kind} {name}"
    start = starts[0].start()
    next_decl = re.search(r"(?m)^\s*(?:/--.*?-/\s*)?(?:@[^[\n]+\]\s*)*(?:theorem|lemma|def|namespace|section|end|/-!)\b", text[starts[0].end():])
    end = starts[0].end() + next_decl.start() if next_decl else len(text)
    return text[start:end]


def test_cartan_projector_idempotence_uses_local_expansion_roots() -> None:
    text = OWNER.read_text(encoding="utf-8")
    plus = decl_block(text, "lemma", "Pplus_idempotent")
    minus = decl_block(text, "lemma", "Pminus_idempotent")
    assert "have h_expand" in plus
    assert "have h_expand" in minus
    assert "θ * θ" in plus and "hθ" in plus
    assert "θ * θ" in minus and "hθ" in minus
    assert "Pplus_square_numerator" not in text
    assert "Pminus_square_numerator" not in text


def test_kkt_projector_idempotence_consumes_cartan_projector_roots() -> None:
    text = CONSUMER.read_text(encoding="utf-8")
    plus = decl_block(text, "theorem", "plusProjector_idempotent")
    minus = decl_block(text, "theorem", "minusProjector_idempotent")
    assert "Pplus_idempotent" in plus
    assert "Pminus_idempotent" in minus
    assert "Pplus_square_numerator" not in plus
    assert "Pminus_square_numerator" not in minus
