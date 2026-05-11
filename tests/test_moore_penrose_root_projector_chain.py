from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
OWNER = REPO / "lean" / "InfoGeometry" / "Canonical" / "MoorePenrose.lean"
CONSUMER = REPO / "lean" / "InfoGeometry" / "Canonical" / "CertifiedInverseKernel.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    match = re.search(
        rf"(?ms)^\s*(?:/--.*?-/[\n\s]*)?(?:@[^[\n]+\n\s*)*{kind}\s+{re.escape(name)}(?:\s|:|\().*?(?=^\s*(?:/--.*?-/\s*)?(?:@[^[\n]+\n\s*)*(?:theorem|lemma|def|namespace|section|end|/-!)\b|\Z)",
        text,
    )
    assert match, f"missing {kind} {name}"
    return match.group(0)


def test_moore_penrose_owner_has_beginning_projector_root_lemmas() -> None:
    text = OWNER.read_text(encoding="utf-8")
    assert "lemma right_projector_idempotent_root" not in text
    assert "lemma left_projector_idempotent_root" not in text
    right_export = decl_block(text, "theorem", "rightProjector_idempotent")
    left_export = decl_block(text, "theorem", "leftProjector_idempotent")
    assert "h.aba_eq_a" in right_export
    assert "h.bab_eq_b" in left_export
    assert "calc" in right_export
    assert "calc" in left_export


def test_certified_inverse_kernel_consumes_moore_penrose_projector_exports() -> None:
    text = CONSUMER.read_text(encoding="utf-8")
    mp_range = decl_block(text, "theorem", "mpRangeProjector_idempotent")
    metric = decl_block(text, "theorem", "metricProjector_idempotent")
    assert "IsMoorePenroseInverse.rightProjector_idempotent" in mp_range
    assert "IsMoorePenroseInverse.leftProjector_idempotent" in metric
    assert "right_projector_idempotent_root" not in mp_range
    assert "left_projector_idempotent_root" not in metric
