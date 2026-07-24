from pathlib import Path

import pytest


BASE = Path(__file__).resolve().parents[1] / "docs"
RAW_MAP = BASE / "automath_declaration_raw_name_map.json"
CORRESPONDENCE = BASE / "automath_10_branch_prefix_correspondence.json"


def _load_json(path: Path):
    import json
    return json.loads(path.read_text())


def test_automath_declaration_raw_name_map_exists_and_nonempty():
    assert RAW_MAP.exists()
    data = _load_json(RAW_MAP)
    assert isinstance(data, list)
    assert len(data) > 0


def test_automath_10_branch_prefix_correspondence_exists_and_nonempty():
    assert CORRESPONDENCE.exists()
    data = _load_json(CORRESPONDENCE)
    assert isinstance(data, list)
    assert len(data) > 0


def test_10_branch_correspondence_has_self_affine_module_entry():
    data = _load_json(CORRESPONDENCE)
    files = {item["source_file"] for item in data}
    assert "lean/Omega/Zeta/XiZgAddressBinarySelfAffine.lean" in files
    assert "lean/InfoGeometry/External/Automath/Omega/Zeta/XiZgAddressBinarySelfAffine.lean" in files


def test_10_branch_correspondence_prefix_keys():
    data = _load_json(CORRESPONDENCE)
    expected_prefixes = {
        "xi_zg_address_binary_self_affine_prefix_zero",
        "xi_zg_address_binary_self_affine_prefix_one_zero",
    }
    for item in data:
        prefixes = set(item.get("prefix_names", []))
        assert expected_prefixes.issubset(prefixes)


def test_10_branch_correspondence_paper_label():
    data = _load_json(CORRESPONDENCE)
    for item in data:
        assert item.get("paper_label") == "thm:xi-zg-address-binary-self-affine"


def test_10_branch_correspondence_evidence_checks():
    data = _load_json(CORRESPONDENCE)
    for item in data:
        checks = item.get("evidence_checks", {})
        assert checks.get("forced_10_mentioned") is True
        assert checks.get("prefix_10_present") is True
        assert checks.get("injective_found") is True
        assert checks.get("disjoint_found") is True
        assert checks.get("prefix_map_decomp_found") is True
