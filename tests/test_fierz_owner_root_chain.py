from pathlib import Path
import re


REPO = Path(__file__).resolve().parents[1]
FIERZ_READOUT = REPO / "lean" / "InfoGeometry" / "Canonical" / "FierzReadout.lean"
QUANTUM_FIERZ = REPO / "lean" / "InfoGeometry" / "Quantum" / "Fierz.lean"


def theorem_block(text: str, name: str) -> str:
    match = re.search(rf"(?ms)^\s*(?:@[^[\n]+\n\s*)*theorem\s+{re.escape(name)}\b.*?(?=^\s*(?:@[^[\n]+\n\s*)*(?:theorem|def|structure|namespace|end)\b|\Z)", text)
    assert match, f"missing theorem {name}"
    return match.group(0)


def test_doubled_fierz_majorana_uses_owner_root_not_generic_wrapper() -> None:
    text = FIERZ_READOUT.read_text(encoding="utf-8")
    block = theorem_block(text, "doubledFierz_majorana")
    assert "doubledFierzReadout_isMajoranaShadow_iff" in block
    assert "information_fierz_majorana" in block
    assert "FierzChannelReadout.fierz_majorana" not in block


def test_quantum_fierz_owner_roots_are_present() -> None:
    text = QUANTUM_FIERZ.read_text(encoding="utf-8")
    identity = theorem_block(text, "information_fierz_identity")
    assert "hessian_indefinite_form_explicit" in identity
    assert "inducedSymplecticForm" in identity
    assert "ring" in identity
    majorana = theorem_block(text, "information_fierz_majorana")
    assert "information_fierz_identity" in majorana
    assert "ring" in majorana
