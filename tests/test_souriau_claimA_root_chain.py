from pathlib import Path
import re


REPO = Path(__file__).resolve().parents[1]
TRANSLATOR = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauTheoremTranslatorPacket.lean"
OWNER = REPO / "lean" / "InfoGeometry" / "Canonical" / "SouriauThermodynamics.lean"


def theorem_block(text: str, name: str) -> str:
    match = re.search(rf"(?ms)^\s*(?:@[^[\n]+\n\s*)*theorem\s+{re.escape(name)}\b.*?(?=^\s*(?:@[^[\n]+\n\s*)*(?:theorem|def|structure|section|namespace|end|/-!)\b|\Z)", text)
    assert match, f"missing theorem {name}"
    return match.group(0)


def test_claimA_translator_inlines_partition_log_root_chain() -> None:
    text = TRANSLATOR.read_text(encoding="utf-8")
    block = theorem_block(text, "claimA_massieu_eq_log_partition")
    assert "rw [souriauMassieuPotential, potentialGC, souriauPartition_eq_partitionGC]" in block
    assert "souriauMassieuPotential_eq_log_partition M T" not in block


def test_souriau_partition_owner_root_is_definitional_log_partition_chain() -> None:
    text = OWNER.read_text(encoding="utf-8")
    block = theorem_block(text, "souriauMassieuPotential_eq_log_partition")
    assert "souriauMassieuPotential" in block
    assert "potentialGC" in block
    assert "souriauPartition_eq_partitionGC" in block
    assert "rw [souriauMassieuPotential, potentialGC, souriauPartition_eq_partitionGC]" in block
