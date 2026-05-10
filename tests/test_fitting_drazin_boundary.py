from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
DRAZIN = REPO / "lean" / "InfoGeometry" / "Canonical" / "Drazin.lean"


def decl_block(text: str, kind: str, name: str) -> str:
    starts = list(re.finditer(rf"(?m)^\s*(?:@\[[^\n]+\]\s*)*{kind}\s+{re.escape(name)}(?:\s|:|\().*$", text))
    assert starts, f"missing {kind} {name}"
    start = starts[0].start()
    line_end = text.find("\n", starts[0].end())
    search_from = line_end + 1 if line_end != -1 else starts[0].end()
    nxt = re.search(
        r"(?m)^\s*(?:/-!|section|end|namespace|@\[[^\n]+\]\s*)*(?:lemma|theorem|def|noncomputable def|abbrev|noncomputable abbrev)\s+",
        text[search_from:],
    )
    end = search_from + nxt.start() if nxt else len(text)
    return text[start:end]


def test_fitting_drazin_boundary_defines_regular_and_nilpotent_parts():
    text = DRAZIN.read_text()
    regular = decl_block(text, "def", "fittingRegularPart")
    nilpotent = decl_block(text, "def", "fittingNilpotentPart")
    assert "a * projection a b" in regular
    assert "a * complementaryProjection a b" in nilpotent


def test_fitting_drazin_decomposition_is_algebraic_not_witness_packaging():
    text = DRAZIN.read_text()
    block = decl_block(text, "theorem", "fittingRegularPart_add_fittingNilpotentPart_eq_self")
    assert "fittingRegularPart a b + fittingNilpotentPart a b = a" in block
    assert "unfold fittingRegularPart fittingNilpotentPart complementaryProjection projection" in block
    assert "noncomm_ring" in block
    forbidden = ["True", "Exists", "Nonempty", "by trivial", "admit", "sorry"]
    assert not any(token in block for token in forbidden)


def test_fitting_drazin_complement_annihilation_roots_in_power_law_and_commutation():
    text = DRAZIN.read_text()
    left = decl_block(text, "theorem", "power_mul_complementaryProjection_eq_zero")
    right = decl_block(text, "theorem", "complementaryProjection_mul_power_eq_zero")
    assert "a^k * complementaryProjection a b = 0" in left
    assert "h.power" in left
    assert "pow_succ" in left
    assert "complementaryProjection a b * a^k = 0" in right
    assert "power_mul_complementaryProjection_eq_zero h" in right
    assert "complementaryProjection_comm_self h" in right


def test_fitting_nilpotent_part_has_explicit_power_zero_boundary():
    text = DRAZIN.read_text()
    block = decl_block(text, "theorem", "fittingNilpotentPart_pow_succ_eq_zero")
    assert "(fittingNilpotentPart a b)^(k + 1) = 0" in block
    assert "power_le h (Nat.le_succ k)" in block
    assert "complementaryProjection_is_idempotent h" in block
    assert "pow_succ_eq_of_idempotent" in block
    forbidden = ["IsNilpotent", "True", "Exists", "Nonempty", "by trivial", "admit", "sorry"]
    assert not any(token in block for token in forbidden)
